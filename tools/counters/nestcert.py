#!/usr/bin/env python3
"""UNTRUSTED: the NESTED overflow branch -- search, validation and Coq glue.

The residue's dominant class (492 of the 883 unproven rows, `ovfshape.py`) is
`AFFINE`/`EXP2`: an ordinary affine interior lap and an overflow that costs
`Theta(2^j)`, because the machine counts its whole range a second time in a
shifted frame before the outer msb bumps.  `docs/NESTED_LAP_PLAN.md` retires
the premise that this needs a new count language -- `LapStep` only asks for
`exists n` -- and `theories/Counters/NestedLap.v` is the composition theorem:

    boot   (affine chain)   Cc p            -> Cin v0
    inner  (INDUCTION)      Cin v0          -> Cin (fill v0)     [exists n]
    exit   (affine chain)   Cin (fill v0)   -> Cc (Pos.succ p)   [up to lift]

This module is Part 3, the emitter side.  It supplies `emit_lapcert.derive`
with a nested overflow branch wherever the flat one raises `no overflow
chain`, and `emit_lapcert.render` with the extra Coq.

TWO THINGS MAKE IT DERIVE, and both are measured (`tools/counters/nestboot2.py`,
30 machines of the bucket, K = 6; table in `docs/NESTED_LAP_PLAN.md`):

  * enumerate every inner key rather than ranking them (wave-13 section 4.1);
  * accept the two inner JOINTS up to `lift`.  `nestboot.py` predates wave-16
    and asked for syntactic equality, which is stricter than the theorem --
    the same defect wave-16 found on the interior branch.  With both:
    7/30 -> 17/30 boot+exit+inner-lap.

The inner alphabet is searched INDEPENDENTLY of the outer one: 37% of these
machines have inner != outer (`Alph_10_11_11 -> Ip` on 51 of 144), which is
why `emit_ixp.py` -- `Ip` at both levels -- derives 0 of the bucket.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
from emit_interleave import carry                                  # noqa: E402

LAB = 'ABCD'

# How many cells past the decoded word an inner key may carry.
#
# MEASURED, and it is a do-not-retry: at 6 a key appears on 13 of 40 machines
# that report "no inner family" at 3 (and [K] = 5, 6 or 7 changes nothing, so
# the tail length is the binding constraint on FINDING a family, not the
# octave) -- but re-running the whole 299-machine failure set at 6 boards
# ZERO.  33 machines move from "no inner family" to "no boot chain"/"no exit
# chain", i.e. the longer-tailed families exist and no chain lands on them.
# Key counts are 0-4, so the [maxkeys] cap is not what is binding either.
MAXTAIL = 3


class NestError(Exception):
    """This machine does not take the nested route."""


# How far a key got, so a machine is filed under its BEST key's blocker.
_RANK = {
    'no boot chain': 0,
    'no exit chain': 1,
    'no inner interior chain': 2,
    'boot of zero length at j=0': 3,
    'inner lap of zero length at i=0': 3,
}


# --------------------------------------------------------------- the search ---

def decode(word, A, B, C):
    """word = E(v) -> v, by stripping A/B off the front until C remains."""
    w, bits = tuple(word), []
    for _ in range(64):
        if w == C:
            v = 1
            for b in reversed(bits):
                v = 2 * v + b
            return v
        if len(w) >= len(A) and w[:len(A)] == A:
            bits.append(0)
            w = w[len(A):]
        elif len(w) >= len(B) and w[:len(B)] == B:
            bits.append(1)
            w = w[len(B):]
        else:
            return None
    return None


def phase_mid(tab, st0, encf, tail, far, K=6, maxT=400000):
    """Every blank-head configuration inside ONE overflow phase of the given
    outer anchor, in order.  Raises if the phase does not close."""
    tail, far = tuple(tail), tuple(far)
    cfg = (st0, tuple(encf(2 ** K - 1)) + tail, 0, far)
    want = (st0, LC.rstrip0(tuple(encf(2 ** K)) + tail), 0, LC.rstrip0(far))
    mid = []
    for _ in range(maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        q, l, h, r = cfg
        if (q == want[0] and h == want[2] and LC.rstrip0(l) == want[1]
                and LC.rstrip0(r) == want[3]):
            return mid
        if h == 0:
            mid.append((q, LC.rstrip0(l), LC.rstrip0(r)))
    raise NestError('no overflow phase at K=%d' % K)


def families(mid, ENCDATA, ENCS, K=6, maxtail=MAXTAIL):
    """Every (alphabet, state, tail, far) in [mid] whose decoded values run
    exactly 2^(K-1) .. 2^K-1.

    Returned MOST-HITS-FIRST, but the caller must ENUMERATE: the best-scoring
    key is measured never to be the one the boot lands on.

    [maxtail] is how many cells past the decoded word the key may carry; see
    [MAXTAIL] for why it is 3 and not 6.
    """
    hits = {}
    for (q, l, r) in mid:
        for name in ENCS:
            d = ENCDATA[name]
            if d['obS'] != 0:
                # obS >= 1 alphabets frame the all-ones anchor differently;
                # the [pow2]/[fill] glue below assumes soS = soD = C.
                continue
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(maxtail + 1):
                if k > len(l) - 1:
                    break
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = decode(head, A, B, C)
                if v is not None:
                    hits.setdefault((name, q, tl, r), []).append(v)
    want_run = list(range(2 ** (K - 1), 2 ** K))
    keys = [(k, len(v)) for k, v in hits.items() if v == want_run]
    keys.sort(key=lambda kv: -kv[1])
    return [k for k, _ in keys]


def split_at_fill(mid, ENC, key, K=6):
    """[mid] after the FIRST configuration at which [key]'s counter is all
    ones -- i.e. the part of the phase the exit chain has to cross.

    WAVE18 section 4c: on the machines whose exit measures EXPONENTIAL this
    half carries a SECOND consecutive family, at the same state and alphabet
    with a shifted tail.  That is the sync-bouncer shape, "count 8->15, shift,
    count 8->15 again".
    """
    name_in, st_in, ti, fi = key
    w = LC.rstrip0(tuple(ENC[name_in](2 ** K - 1)) + tuple(ti))
    wf = LC.rstrip0(tuple(fi))
    for i, (q, l, r) in enumerate(mid):
        if q == st_in and l == w and r == wf:
            return mid[i:]
    return []


def inner_keys(tab, ENCDATA, ENCS, st0, encf, tail, far, K=6,
               maxT=400000, maxtail=MAXTAIL):
    """[families] over a whole phase -- kept as the one-call entry point the
    probes (`nestboot2.py`, `bootshape2.py`) use."""
    return families(phase_mid(tab, st0, encf, tail, far, K, maxT),
                    ENCDATA, ENCS, K, maxtail)


# ------------------------------------------------------- the four endpoints ---

def endpoints(ENCDATA, enc, st0, tail, far, key):
    """B0 is `emit_lapcert.confs`'s overflow start and is passed in by the
    caller; the other three are built here.

      inner start  CinS = rep uD_in j ++ soD_in ++ tail_in   ( = E_in (pow2 j))
      inner fill   CinF = rep uS_in j ++ soS_in ++ tail_in   ( = E_in (fill _))
      inner lap    AI0  = rep uS_in i ++ sS_in   / AI1 = rep uD_in i ++ sD_in
    """
    name_in, st_in, tail_in, far_in = key
    din = ENCDATA[name_in]
    Fin = (tuple(far_in), (), 0, 0, ())
    ti = tuple(tail_in)
    CinS = (st_in, ((), din['uD'], 1, 0, din['soD'] + ti), 0, Fin)
    CinF = (st_in, ((), din['uS'], 1, 0, din['soS'] + ti), 0, Fin)
    AI0 = (st_in, ((), din['uS'], 1, 0, din['sS']), 0, Fin)
    AI1 = (st_in, ((), din['uD'], 1, 0, din['sD']), 0, Fin)
    return CinS, CinF, AI0, AI1


def _chain(tab, el, er, a, b):
    """Exact first, then up to [lift] -- the wave-16 preference order."""
    for lift in (False, True):
        try:
            ch = LC.derive_chain(tab, el, er, a, b, lift=lift)
        except Exception:                                          # noqa: BLE001
            ch = None
        if ch is not None:
            return ch, lift
    return None, None


def _slack(side, want, what):
    """A reached side must be the wanted one plus TRAILING BLANKS.  Returns
    the number of surplus blanks; raises if the difference is anything else."""
    got = tuple(side)
    want = tuple(want)
    n = len(got) - len(want)
    if n < 0 or got[:len(want)] != want or any(got[len(want):]):
        raise NestError('%s slack %r vs %r' % (what, got, want))
    return n


# ------------------------------------------------------------- the derivation ---

def derive_nested(tab, ENCDATA, ENCS, ENC, enc, st0, tail, far, B0, B1,
                  K=6, maxkeys=40):
    """Search the inner family and derive the three chains.  ENUMERATES the
    keys -- the best-scoring one is measured never to be the one the boot can
    land on.  Raises [NestError] with the reason if none works."""
    encf = ENC[enc]
    mid = phase_mid(tab, st0, encf, tail, far, K)
    keys = families(mid, ENCDATA, ENCS, K)
    if not keys:
        raise NestError('no inner family at pow2 j')
    # Report the FURTHEST any key got, not the last one tried.  The first
    # version kept the last, so a machine whose best key derived a boot and
    # failed on the exit was filed under whatever its final key did -- which
    # made the failure profile point at the wrong stage.
    best, last = -1, 'no inner family'
    for key in keys[:maxkeys]:
        try:
            return build(tab, ENCDATA, ENCS, encf, enc, st0, tail, far, B0,
                         B1, key, ENC, mid, K)
        except NestError as e:
            r = _RANK.get(str(e).split(' slack')[0], len(_RANK))
            if r > best:
                best, last = r, str(e)
    raise NestError(last)


def _land(conf, st, d, post_want, far_want, what):
    """A reached endpoint must be the anchor's syntactic shape plus TRAILING
    BLANKS on each side, and nothing else.  Returns (post pad, far pad)."""
    if conf[0] != st or conf[2] != 0:
        raise NestError('%s lands in the wrong state/head' % what)
    lpre, lu, la, lb, lpost = conf[1]
    if lpre or tuple(lu) != tuple(d) or (la, lb) != (1, 0):
        raise NestError('%s rep shape %r' % (what, (conf[1],)))
    pad = _slack(lpost, post_want, what + ' post')
    if conf[3][1]:
        raise NestError('%s far side carries a rep' % what)
    return pad, _slack(tuple(conf[3][0]) + tuple(conf[3][4]), far_want,
                       what + ' far')


def _inner_lap(tab, ENCDATA, key):
    """The inner family's own interior lap: chain, srun, landing pads."""
    name_in, st_in, tail_in, far_in = key
    din = ENCDATA[name_in]
    AI0, AI1 = endpoints(ENCDATA, None, None, (), (), key)[2:]
    chn, _ = _chain(tab, False, True, AI0, AI1)
    if chn is None:
        raise NestError('no inner interior chain')
    rn = LC.srun(tab, False, True, chn, AI0)
    if rn is None:
        raise NestError('internal: srun disagrees with the search')
    if rn[2] == 0:
        raise NestError('inner lap of zero length at i=0')
    ipad, ifar = _land(rn[0], st_in, din['uD'], tuple(din['sD']),
                       tuple(far_in), 'inner lap')
    return dict(AI0=AI0, AI1=rn[0], chn=chn, cn=(rn[1], rn[2]),
                ipad=ipad, ifar=ifar)


def build(tab, ENCDATA, ENCS, encf, enc, st0, tail, far, B0, B1, key, ENC,
          mid, K=6):
    name_in, st_in, tail_in, far_in = key
    din, dout = ENCDATA[name_in], ENCDATA[enc]
    CinS, CinF, AI0, AI1 = endpoints(ENCDATA, enc, st0, tail, far, key)

    chb, _ = _chain(tab, True, True, B0, CinS)
    if chb is None:
        raise NestError('no boot chain')
    lap1 = _inner_lap(tab, ENCDATA, key)
    chn, rn = lap1['chn'], (None, lap1['cn'][0], lap1['cn'][1])

    two = None
    che, _ = _chain(tab, True, True, CinF, B1)
    if che is None:
        # WAVE18 section 4c: the exit is EXPONENTIAL because the phase runs a
        # SECOND count in a shifted frame.  Split at the first fill and look
        # for it; [NestedLap2.boot_via_fill] folds the first count into the
        # boot, so no new composition theorem is needed.
        two = _second_count(tab, ENCDATA, ENCS, ENC, CinF, B1, mid, key, K)
        che, CinF2 = two['che'], two['BE0']
    rb = LC.srun(tab, True, True, chb, B0)
    re = LC.srun(tab, True, True, che, two['BE0'] if two else CinF)
    if rb is None or re is None:
        raise NestError('internal: srun disagrees with the search')
    if rb[2] == 0:
        raise NestError('boot of zero length at j=0')

    # The boot's landing shape: the inner anchor plus TRAILING BLANKS.
    BB1 = rb[0]
    bpad, bfar = _land(BB1, st_in, din['uD'],
                       tuple(din['soD']) + tuple(tail_in), tuple(far_in),
                       'boot')

    # The exit's landing shape is checked by [emit_lapcert.render]'s existing
    # [geo_] machinery (it is an ordinary overflow endpoint); all this needs
    # is how many blanks past the anchor's FAR side it stopped.
    if re[0][3][1]:
        raise NestError('exit far side carries a rep')
    efar = _slack(tuple(re[0][3][0]) + tuple(re[0][3][4]), tuple(far),
                  'exit far')

    d = dict(inner=name_in, st_in=st_in, tail_in=list(tail_in),
             far_in=list(far_in),
             chb=chb, BB1=BB1, cb=(rb[1], rb[2]),
             che=che, BE0=(two['BE0'] if two else CinF), BE1=re[0],
             ce=(re[1], re[2]),
             chn=lap1['chn'], AI0=lap1['AI0'], AI1=lap1['AI1'],
             cn=lap1['cn'],
             bpad=bpad, bfar=bfar, ipad=lap1['ipad'], ifar=lap1['ifar'],
             efar=efar, two=two)
    validate(tab, ENC, encf, enc, ENCDATA, st0, tail, far, key, d)
    return d


def _second_count(tab, ENCDATA, ENCS, ENC, CinF, B1, mid, key, K,
                  maxkeys=40):
    """The SHIFT and the SECOND count.  [CinF] is the first family's all-ones
    fill -- where the exit chain would have started and could not."""
    post = split_at_fill(mid, ENC, key, K)
    if not post:
        raise NestError('no exit chain')
    keys2 = families(post, ENCDATA, ENCS, K)
    keys2 = [k for k in keys2 if k != key]
    if not keys2:
        raise NestError('no exit chain')
    last = 'no shift chain'
    for k2 in keys2[:maxkeys]:
        try:
            name2, st2, ti2, fi2 = k2
            d2 = ENCDATA[name2]
            CinS2, CinF2, _, _ = endpoints(ENCDATA, None, None, (), (), k2)
            chm, _ = _chain(tab, True, True, CinF, CinS2)
            if chm is None:
                raise NestError('no shift chain')
            che, _ = _chain(tab, True, True, CinF2, B1)
            if che is None:
                raise NestError('no second exit chain')
            lap2 = _inner_lap(tab, ENCDATA, k2)
            rm = LC.srun(tab, True, True, chm, CinF)
            if rm is None:
                raise NestError('internal: srun disagrees with the search')
            mpad, mfar = _land(rm[0], st2, d2['uD'],
                               tuple(d2['soD']) + tuple(ti2), tuple(fi2),
                               'shift')
            return dict(inner=name2, st_in=st2, tail_in=list(ti2),
                        far_in=list(fi2),
                        chm=chm, BM0=CinF, BM1=rm[0], cm=(rm[1], rm[2]),
                        # the pads of the chain INTO this family, named the
                        # same as the first family's so [_fam_reps] is shared
                        bpad=mpad, bfar=mfar,
                        che=che, BE0=CinF2,
                        chn=lap2['chn'], AI0=lap2['AI0'], AI1=lap2['AI1'],
                        cn=lap2['cn'], ipad=lap2['ipad'], ifar=lap2['ifar'])
        except NestError as e:
            last = str(e)
    raise NestError(last)


# -------------------------------------------------------------- validation ---

def _sim(tab, cfg, n):
    for _ in range(n):
        cfg = LC.wstep(tab, False, False, cfg)
    return cfg


def _eqlift(a, b):
    return (a[0] == b[0] and a[2] == b[2]
            and LC.rstrip0(a[1]) == LC.rstrip0(b[1])
            and LC.rstrip0(a[3]) == LC.rstrip0(b[3]))


def validate(tab, ENC, encf, enc, ENCDATA, st0, tail, far, key, d, jlo=2,
             jhi=7):
    """Differentially check ALL THREE pieces against the raw simulator --
    exact step counts and exact configurations, over a range of outer indices.

    The inner lap is checked at every inner value of the phase, so the
    Theta(2^j) run itself is replayed, not merely its endpoints."""
    name_in, st_in, tail_in, far_in = key
    tail, far = tuple(tail), tuple(far)
    ti, fi = tuple(tail_in), tuple(far_in)
    encin = ENC[name_in]
    n = 0
    two = d.get('two')
    if two:
        enc2 = ENC[two['inner']]
        st2, ti2, fi2 = two['st_in'], tuple(two['tail_in']), tuple(two['far_in'])

    def laps(st, encx, tx, fx, cn, v0, vf, what):
        for v in range(v0, vf):
            i, ov = carry(v)
            if ov:
                raise NestError('internal: inner overflow inside the run')
            a = (st, tuple(encx(v)) + tx, 0, fx)
            b = (st, tuple(encx(v + 1)) + tx, 0, fx)
            g = _sim(tab, a, cn[0] * i + cn[1])
            if not _eqlift(g, b):
                raise NestError('validate %s v=%d: %r want %r'
                                % (what, v, g, b))

    for j in range(jlo, jhi + 1):
        p = 2 ** (j + 1) - 1                        # cview p = (S j, None)
        v0, vf = 2 ** j, 2 ** (j + 1) - 1
        # boot
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st_in, tuple(encin(v0)) + ti, 0, fi)
        got = _sim(tab, start, d['cb'][0] * j + d['cb'][1])
        if not _eqlift(got, want):
            raise NestError('validate boot j=%d: %r want %r' % (j, got, want))
        # the first count
        laps(st_in, encin, ti, fi, d['cn'], v0, vf, 'inner')
        if two:
            # the SHIFT, then the second count
            start = (st_in, tuple(encin(vf)) + ti, 0, fi)
            want = (st2, tuple(enc2(v0)) + ti2, 0, fi2)
            got = _sim(tab, start, two['cm'][0] * j + two['cm'][1])
            if not _eqlift(got, want):
                raise NestError('validate shift j=%d: %r want %r'
                                % (j, got, want))
            laps(st2, enc2, ti2, fi2, two['cn'], v0, vf, 'inner2')
            estart = (st2, tuple(enc2(vf)) + ti2, 0, fi2)
        else:
            estart = (st_in, tuple(encin(vf)) + ti, 0, fi)
        # exit
        want = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = _sim(tab, estart, d['ce'][0] * j + d['ce'][1])
        if not _eqlift(got, want):
            raise NestError('validate exit j=%d: %r want %r' % (j, got, want))
        n += 1
    d['nval'] = '%d overflow phases, j = %d..%d (%d inner laps%s)' % (
        n, jlo, jhi,
        sum(2 ** j - 1 for j in range(jlo, jhi + 1)) * (2 if two else 1),
        ', two counts each' if two else '')




# --------------------------------------------------------- family templates ---
#
# A nested board carries ONE or TWO inner families (see WAVE18 section 4c).
# Everything that is per-family -- the anchor, its [pow2] lemma, its own
# interior lap and that lap's two glue lemmas -- is emitted from these, once
# per family, with @S@ the family suffix ('' or '2').

FAM_DEFS = r"""(** ** The @ORD@INNER anchor family -- @ENCI@ at @STI@ *)
Definition Cin@S@_@ID@ (v : positive) : cconf := (@STI@, (@ENCI@ v ++ @TAILI@, S0, @FARI@)).
Local Notation Cin@S@ := Cin@S@_@ID@.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2@S@_@ID@ : forall n, @ENCI@ (pow2 n) = rep @UDI@ n ++ @SODI@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI@S@0_@ID@ : sconf := @AI0@.
Definition AI@S@1_@ID@ : sconf := @AI1@.
Definition chn@S@_@ID@ : list lstep := @CHN@.

Lemma run_inner@S@_@ID@ : srun tm false true chn@S@_@ID@ AI@S@0_@ID@ = Some (AI@S@1_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed."""


FAM_GLUE = r"""Lemma gsn@S@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  Cin@S@ v = cden (@ENCI@ q0 ++ @TAILI@) [] i AI@S@0_@ID@.
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v i q0 E) as (H1 & _).
  unfold Cin@S@_@ID@, cden, AI@S@0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep @USI@ i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen@S@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (@ENCI@ q0 ++ @TAILI@) [] i AI@S@1_@ID@) = lift (Cin@S@ (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v i q0 E) as (_ & H2).
  unfold Cin@S@_@ID@, cden, AI@S@1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
@IFARCHG@  rewrite H2. first [ rewrite <- (app_assoc (rep @UDI@ i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin@S@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin@S@ v) = Some c'
               /\ lift c' = lift (Cin@S@ (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (@CAN@ * i + @CBN@), (cden (@ENCI@ q0 ++ @TAILI@) [] i AI@S@1_@ID@).
  split; [lia|]. split; [| exact (gen@S@_@ID@ v i q0 E)].
  rewrite (gsn@S@_@ID@ v i q0 E).
  exact (srun_sound tm false true chn@S@_@ID@ AI@S@0_@ID@ AI@S@1_@ID@ @CAN@ @CBN@
           run_inner@S@_@ID@ (@ENCI@ q0 ++ @TAILI@) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to @BPAD@/@BFAR@
    trailing blanks. *)
Lemma gbo@S@_@ID@ : forall j, lift (cden [] [] j @LANDC@) = lift (Cin@S@ (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j @LANDC@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, @LANDC@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin@S@ (pow2 j) = (@STI@, (rep @UDI@ j ++ @BWANT@, S0, @FARI@))).
  { unfold Cin@S@_@ID@. rewrite epow2@S@_@ID@.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi@S@_@ID@ : forall j, Cin@S@ (fill (pow2 j)) = cden [] [] j @FILLC@.
Proof.
  intro j.
  destruct (@ENCMODI@.@NONEI@ (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin@S@_@ID@, cden, @FILLC@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed."""


def _fam_reps(ENCDATA, N, clist, cconf, cchain, ST, suffix, ordinal,
              landc, fillc):
    """The per-family holes.  [N] is the family record (the top-level nest
    dict, or its ['two'] sub-dict)."""
    din = ENCDATA[N['inner']]
    ti, fi = tuple(N['tail_in']), tuple(N['far_in'])
    bwant = tuple(din['soD']) + ti
    pad, farpad = N['bpad'], N['bfar']
    bleft = ('(' * pad + 'rep %s j ++ %s' % (clist(din['uD']), clist(bwant))
             + ''.join(') ++ [S0]' for _ in range(pad)))
    bfare = ('(' * farpad + clist(fi)
             + ''.join(') ++ [S0]' for _ in range(farpad)))
    ifarb = clist(tuple(fi) + (0,) * N['ifar'])
    ifarnest = ('(' * N['ifar'] + clist(fi)
                + ''.join(') ++ [S0]' for _ in range(N['ifar'])))
    return {
        '@S@': suffix, '@ORD@': ordinal,
        '@ENCI@': din.get('fn', N['inner']),
        '@ENCMODI@': din['mod'], '@SOMEI@': din['some'], '@NONEI@': din['none'],
        '@STI@': ST[N['st_in']], '@TAILI@': clist(ti), '@FARI@': clist(fi),
        '@USI@': clist(din['uS']), '@UDI@': clist(din['uD']),
        '@SDI@': clist(din['sD']), '@SODI@': clist(din['soD']),
        '@AI0@': cconf(N['AI0']), '@AI1@': cconf(N['AI1']),
        '@CHN@': cchain(N['chn']),
        '@CAN@': str(N['cn'][0]), '@CBN@': str(N['cn'][1]),
        '@BPAD@': str(pad), '@BFAR@': str(farpad),
        '@BLEFT@': bleft, '@BFARE@': bfare, '@BWANT@': clist(bwant),
        '@LANDC@': landc, '@FILLC@': fillc,
        '@IFARCHG@': ('' if N['ifar'] == 0 else
                      '  change (%s) with (%s).\n  rewrite !lift_app_blank.\n'
                      % (ifarb, ifarnest)),
    }


def _fill(tpl, reps):
    for k, v in reps.items():
        tpl = tpl.replace(k, v)
    return tpl


# ------------------------------------------------------------ Coq emission ---
#
# The nested overflow branch replaces the flat one.  Everything ELSE in the
# board -- the anchor, the interior branch, the bootstrap, the visits and the
# closer -- is unchanged, because [nested_overflow_lift]'s conclusion is
# verbatim what [lap_of_run] produced: the [LapStep] obligation for one
# overflow anchor.  That is the whole point of the composition theorem.

NEST_CHAINS = r"""(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_@ID@ : sconf := @BB1@.
Definition chb_@ID@ : list lstep := @CHB@.

Lemma run_boot_@ID@ : srun tm true true chb_@ID@ B0_@ID@ = Some (BB1_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.
@SHIFTDEF@
(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_@ID@ : sconf := @BE0@.
Definition che_@ID@ : list lstep := @CHE@.

Lemma run_exit_@ID@ : srun tm true true che_@ID@ BE0_@ID@ = Some (B1_@ID@, @CAO@, @CBO@).
Proof. vm_compute. reflexivity. Qed."""


SHIFT_DEF = r"""
(** *** shift: the FIRST count's all-ones fill -> the SECOND count's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_@ID@ : sconf := @BM0@.
Definition BM1_@ID@ : sconf := @BM1@.
Definition chm_@ID@ : list lstep := @CHM@.

Lemma run_shift_@ID@ : srun tm true true chm_@ID@ BM0_@ID@ = Some (BM1_@ID@, @CAM@, @CBM@).
Proof. vm_compute. reflexivity. Qed.
"""


LAPIL = r"""(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. @LAPIL@ Qed."""


BOOT1 = r"""    exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).
    split; [lia|]. split; [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j E).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity))."""


BOOT2 = r"""    apply (boot_via_fill tm Cc Cin Cin2 lapin_@ID@ p (pow2 j) (pow2 j)).
    + exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).
      split; [lia|]. split; [| exact (gbo_@ID@ j)].
      rewrite (gso_@ID@ p j E).
      exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
               run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
    + exists (@CAM@ * j + @CBM@), (cden [] [] j BM1_@ID@).
      split; [| exact (gbo2_@ID@ j)].
      rewrite (gxi_@ID@ j).
      exact (srun_sound tm true true chm_@ID@ BM0_@ID@ BM1_@ID@ @CAM@ @CBM@
               run_shift_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity))."""


LAPO = r"""(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin@LAST@ lapin@LAST@_@ID@ p (pow2 j)).
  - @BOOT@
  - exists (@CAO@ * j + @CBO@), (cden [] [] j B1_@ID@).
    split; [| exact (geo_@ID@ p j E)].
    rewrite (gxi@LAST@_@ID@ j).
    exact (srun_sound tm true true che_@ID@ BE0_@ID@ B1_@ID@ @CAO@ @CBO@
             run_exit_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed."""


NEST_VISX = r"""(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by boot + the inner counter's own laps + that prefix. *)
Lemma visx_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  apply (vis_via_fill tm Cc Cin lapin_@ID@ q p (pow2 j)).
  - exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@). split;
      [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j E).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - apply (vis_lift_of_csteps tm (fun _ : positive => Cin (fill (pow2 j))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin (fill (pow2 j)))
                      true true l BE0_@ID@ xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi_@ID@ j)].
Qed."""


NEST_OVFCASE = r"""  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_@ID@ p j' E)."""


def nest_defs(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The DEFINITIONS block: one per family, then the chains."""
    N = D['nest']
    two = N.get('two')
    fams = _fill(FAM_DEFS, _fam_reps(ENCDATA, N, clist, cconf, cchain, ST,
                                     '', 'FIRST ' if two else '', '', ''))
    if two:
        fams += '\n\n' + _fill(FAM_DEFS,
                                _fam_reps(ENCDATA, two, clist, cconf, cchain,
                                          ST, '2', 'SECOND ', '', ''))
    chains = NEST_CHAINS.replace('@SHIFTDEF@', SHIFT_DEF if two else '')
    return fams + '\n\n' + chains


def nest_glue(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The GLUE block: one per family, then [lapil_], [lapo_] and [visx_]."""
    N = D['nest']
    two = N.get('two')
    out = _fill(FAM_GLUE, _fam_reps(ENCDATA, N, clist, cconf, cchain, ST, '',
                                    '', 'BB1_@ID@',
                                    'BM0_@ID@' if two else 'BE0_@ID@'))
    if two:
        out += '\n\n' + _fill(FAM_GLUE,
                               _fam_reps(ENCDATA, two, clist, cconf, cchain,
                                         ST, '2', '', 'BM1_@ID@', 'BE0_@ID@'))
    out += '\n\n' + LAPIL
    out += '\n\n' + LAPO.replace('@BOOT@', (BOOT2 if two else BOOT1).strip()) \
                          .replace('@LAST@', '2' if two else '')
    out += '\n\n@VISX@'
    return out


def nest_reps(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The machine-level holes the nested route adds (the per-family ones are
    already substituted by [nest_defs] / [nest_glue])."""
    N = D['nest']
    two = N.get('two')
    din = ENCDATA[N['inner']]
    mods = [din['mod']] + ([ENCDATA[two['inner']]['mod']] if two else [])
    extra = ' '.join(sorted({m for m in mods
                             if m != ENCDATA[D['enc']]['mod']}))
    reps = {
        '@BB1@': cconf(N['BB1']), '@CHB@': cchain(N['chb']),
        '@CAB@': str(N['cb'][0]), '@CBB@': str(N['cb'][1]),
        '@BE0@': cconf(N['BE0']), '@CHE@': cchain(N['che']),
        # [visx_]/[gen_] use LapCertGlueLift's bridges whether or not the
        # OUTER interior lap took the lift route, so it is imported here when
        # @GLUELIFT@ did not already do it.
        '@NESTIMPORT@': (('' if D.get('islack') else ' LapCertGlueLift')
                         + ' IXPGadgets NestedLap NestedLapLift'
                         + (' NestedLap2' if two else '')
                         + ((' ' + extra) if extra else '')),
        '@NVAL@': N['nval'],
        '@LAPIL@': (
            'exact lapi_@ID@.' if D.get('islack') else
            'intros p j q0 E. destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hr).\n'
            '  exists n, (Cc (Pos.succ p)).\n'
            '  split; [exact Hn | split; [exact Hr | reflexivity]].'),
        '@VISX@': (NEST_VISX + '\n\n' if D.get('visx') else ''),
        '@LAST@': '2' if two else '',
    }
    if two:
        reps.update({'@BM0@': cconf(two['BM0']), '@BM1@': cconf(two['BM1']),
                     '@CHM@': cchain(two['chm']),
                     '@CAM@': str(two['cm'][0]), '@CBM@': str(two['cm'][1])})
    return reps
