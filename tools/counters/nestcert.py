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


def inner_keys(tab, ENCDATA, ENCS, st0, encf, tail, far, K=6,
               maxT=400000, maxtail=MAXTAIL):
    """Every (alphabet, state, tail, far) whose decoded values run exactly
    2^(K-1) .. 2^K-1 inside ONE overflow phase of the given outer anchor.

    Keys are returned MOST-HITS-FIRST but the caller must ENUMERATE: the
    best-scoring key is measured never to be the one the boot lands on.

    [maxtail] is how many cells past the decoded word the key may carry; see
    [MAXTAIL] for why it is 3 and not 6.
    """
    tail, far = tuple(tail), tuple(far)
    p, pn = 2 ** K - 1, 2 ** K
    cfg = (st0, tuple(encf(p)) + tail, 0, far)
    want = (st0, tuple(encf(pn)) + tail, 0, far)
    mid, done = [], False
    for _ in range(maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        q, l, h, r = cfg
        if (q == want[0] and h == want[2]
                and LC.rstrip0(l) == LC.rstrip0(want[1])
                and LC.rstrip0(r) == LC.rstrip0(want[3])):
            done = True
            break
        if h == 0:
            mid.append((q, LC.rstrip0(l), LC.rstrip0(r)))
    if not done:
        raise NestError('no overflow phase at K=%d' % K)

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
    keys = inner_keys(tab, ENCDATA, ENCS, st0, encf, tail, far, K)
    if not keys:
        raise NestError('no inner family at pow2 j')
    last = 'no inner family'
    for key in keys[:maxkeys]:
        try:
            return build(tab, ENCDATA, encf, enc, st0, tail, far, B0, B1, key,
                         ENC)
        except NestError as e:
            last = str(e)
    raise NestError(last)


def build(tab, ENCDATA, encf, enc, st0, tail, far, B0, B1, key, ENC):
    name_in, st_in, tail_in, far_in = key
    din, dout = ENCDATA[name_in], ENCDATA[enc]
    CinS, CinF, AI0, AI1 = endpoints(ENCDATA, enc, st0, tail, far, key)

    chb, _ = _chain(tab, True, True, B0, CinS)
    if chb is None:
        raise NestError('no boot chain')
    che, _ = _chain(tab, True, True, CinF, B1)
    if che is None:
        raise NestError('no exit chain')
    chn, _ = _chain(tab, False, True, AI0, AI1)
    if chn is None:
        raise NestError('no inner interior chain')

    rb = LC.srun(tab, True, True, chb, B0)
    re = LC.srun(tab, True, True, che, CinF)
    rn = LC.srun(tab, False, True, chn, AI0)
    if rb is None or re is None or rn is None:
        raise NestError('internal: srun disagrees with the search')
    if rb[2] == 0:
        raise NestError('boot of zero length at j=0')
    if rn[2] == 0:
        raise NestError('inner lap of zero length at i=0')

    # The boot's landing shape.  It must be the inner anchor plus trailing
    # blanks on each side -- [lift] absorbs those and nothing else.
    BB1 = rb[0]
    if BB1[0] != st_in or BB1[2] != 0:
        raise NestError('boot lands in the wrong state/head')
    lpre, lu, la, lb, lpost = BB1[1]
    if lpre or tuple(lu) != tuple(din['uD']) or (la, lb) != (1, 0):
        raise NestError('boot rep shape %r' % (BB1[1],))
    bpad = _slack(lpost, tuple(din['soD']) + tuple(tail_in), 'boot post')
    rpre, ru, ra, rb_, rpost = BB1[3]
    if ru:
        raise NestError('boot far side carries a rep')
    bfar = _slack(tuple(rpre) + tuple(rpost), tuple(far_in), 'boot far')

    # The inner lap's landing shape (same test, at the inner interior anchor).
    AI1r = rn[0]
    if AI1r[0] != st_in or AI1r[2] != 0:
        raise NestError('inner lap lands in the wrong state/head')
    npre, nu, na, nb, npost = AI1r[1]
    if npre or tuple(nu) != tuple(din['uD']) or (na, nb) != (1, 0):
        raise NestError('inner lap rep shape %r' % (AI1r[1],))
    ipad = _slack(npost, tuple(din['sD']), 'inner lap post')
    if AI1r[3][1]:
        raise NestError('inner lap far side carries a rep')
    ifar = _slack(tuple(AI1r[3][0]) + tuple(AI1r[3][4]), tuple(far_in),
                  'inner lap far')

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
             che=che, BE0=CinF, BE1=re[0], ce=(re[1], re[2]),
             chn=chn, AI0=AI0, AI1=AI1r, cn=(rn[1], rn[2]),
             bpad=bpad, bfar=bfar, ipad=ipad, ifar=ifar, efar=efar)
    validate(tab, ENC, encf, enc, ENCDATA, st0, tail, far, key, d)
    return d


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
    for j in range(jlo, jhi + 1):
        p = 2 ** (j + 1) - 1                        # cview p = (S j, None)
        v0, vf = 2 ** j, 2 ** (j + 1) - 1
        # boot
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st_in, tuple(encin(v0)) + ti, 0, fi)
        got = _sim(tab, start, d['cb'][0] * j + d['cb'][1])
        if not _eqlift(got, want):
            raise NestError('validate boot j=%d: %r want %r' % (j, got, want))
        # exit
        start = (st_in, tuple(encin(vf)) + ti, 0, fi)
        want = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = _sim(tab, start, d['ce'][0] * j + d['ce'][1])
        if not _eqlift(got, want):
            raise NestError('validate exit j=%d: %r want %r' % (j, got, want))
        # every inner interior lap of this phase
        for v in range(v0, vf):
            i, ov = carry(v)
            if ov:
                raise NestError('internal: inner overflow inside the run')
            s = (st_in, tuple(encin(v)) + ti, 0, fi)
            w = (st_in, tuple(encin(v + 1)) + ti, 0, fi)
            g = _sim(tab, s, d['cn'][0] * i + d['cn'][1])
            if not _eqlift(g, w):
                raise NestError('validate inner v=%d: %r want %r' % (v, g, w))
        n += 1
    d['nval'] = '%d overflow phases, j = %d..%d (%d inner laps)' % (
        n, jlo, jhi, sum(2 ** j - 1 for j in range(jlo, jhi + 1)))


# ------------------------------------------------------------ Coq emission ---
#
# The nested overflow branch replaces the flat one.  Everything ELSE in the
# board -- the anchor, the interior branch, the bootstrap, the visits and the
# closer -- is unchanged, because [nested_overflow_lift]'s conclusion is
# verbatim what [lap_of_run] produced: the [LapStep] obligation for one
# overflow anchor.  That is the whole point of the composition theorem.

NEST_DEFS = r"""(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the @ENCI@ alphabet at
    state @STI@ -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_@ID@ (v : positive) : cconf := (@STI@, (@ENCI@ v ++ @TAILI@, S0, @FARI@)).
Local Notation Cin := Cin_@ID@.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_@ID@ : forall n, @ENCI@ (pow2 n) = rep @UDI@ n ++ @SODI@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_@ID@ : sconf := @BB1@.
Definition chb_@ID@ : list lstep := @CHB@.

Lemma run_boot_@ID@ : srun tm true true chb_@ID@ B0_@ID@ = Some (BB1_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_@ID@ : sconf := @BE0@.
Definition che_@ID@ : list lstep := @CHE@.

Lemma run_exit_@ID@ : srun tm true true che_@ID@ BE0_@ID@ = Some (B1_@ID@, @CAO@, @CBO@).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_@ID@ : sconf := @AI0@.
Definition AI1_@ID@ : sconf := @AI1@.
Definition chn_@ID@ : list lstep := @CHN@.

Lemma run_inner_@ID@ : srun tm false true chn_@ID@ AI0_@ID@ = Some (AI1_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed."""


NEST_GLUE = r"""(** ** Nested-overflow glue *)

Lemma gsn_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (@ENCI@ q0 ++ @TAILI@) [] i AI0_@ID@.
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v i q0 E) as (H1 & _).
  unfold Cin_@ID@, cden, AI0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep @USI@ i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (@ENCI@ q0 ++ @TAILI@) [] i AI1_@ID@) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v i q0 E) as (_ & H2).
  unfold Cin_@ID@, cden, AI1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
@IFARCHG@  rewrite H2. first [ rewrite <- (app_assoc (rep @UDI@ i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (@CAN@ * i + @CBN@), (cden (@ENCI@ q0 ++ @TAILI@) [] i AI1_@ID@).
  split; [lia|]. split; [| exact (gen_@ID@ v i q0 E)].
  rewrite (gsn_@ID@ v i q0 E).
  exact (srun_sound tm false true chn_@ID@ AI0_@ID@ AI1_@ID@ @CAN@ @CBN@
           run_inner_@ID@ (@ENCI@ q0 ++ @TAILI@) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to @BPAD@/@BFAR@ trailing blanks. *)
Lemma gbo_@ID@ : forall j, lift (cden [] [] j BB1_@ID@) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_@ID@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, BB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (@STI@, (rep @UDI@ j ++ @BWANT@, S0, @FARI@))).
  { unfold Cin_@ID@. rewrite epow2_@ID@.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_@ID@ : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_@ID@.
Proof.
  intro j.
  destruct (@ENCMODI@.@NONEI@ (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_@ID@, cden, BE0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. @LAPIL@ Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_@ID@ p (pow2 j)).
  - exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).
    split; [lia|]. split; [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j E).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (@CAO@ * j + @CBO@), (cden [] [] j B1_@ID@).
    split; [| exact (geo_@ID@ p j E)].
    rewrite (gxi_@ID@ j).
    exact (srun_sound tm true true che_@ID@ BE0_@ID@ B1_@ID@ @CAO@ @CBO@
             run_exit_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed."""


NEST_GLUE = NEST_GLUE + '\n\n@VISX@'

NEST_OVFCASE = r"""  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_@ID@ p j' E)."""


# A state that fires only in the EXIT half.  [vis_of_run] sees a prefix of ONE
# chain, and the overflow lap of a nested machine is three pieces; the boot
# covers the first, this covers the third, and [NestedLapLift.vis_via_fill]
# supplies the exponentially long middle.
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


def nest_reps(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The template holes the nested route adds."""
    N = D['nest']
    din = ENCDATA[N['inner']]
    ti, fi = tuple(N['tail_in']), tuple(N['far_in'])
    bwant = tuple(din['soD']) + ti
    bleft = ('(' * N['bpad'] + 'rep %s j ++ %s' % (clist(din['uD']),
                                                   clist(bwant))
             + ''.join(') ++ [S0]' for _ in range(N['bpad'])))
    bfare = ('(' * N['bfar'] + clist(fi)
             + ''.join(') ++ [S0]' for _ in range(N['bfar'])))
    ifarb = clist(tuple(fi) + (0,) * N['ifar'])
    ifarnest = ('(' * N['ifar'] + clist(fi)
                + ''.join(') ++ [S0]' for _ in range(N['ifar'])))
    return {
        '@ENCI@': din.get('fn', N['inner']),
        '@ENCMODI@': din['mod'], '@SOMEI@': din['some'], '@NONEI@': din['none'],
        '@STI@': ST[N['st_in']], '@TAILI@': clist(ti), '@FARI@': clist(fi),
        '@USI@': clist(din['uS']), '@UDI@': clist(din['uD']),
        '@SDI@': clist(din['sD']), '@SODI@': clist(din['soD']),
        '@BB1@': cconf(N['BB1']), '@CHB@': cchain(N['chb']),
        '@CAB@': str(N['cb'][0]), '@CBB@': str(N['cb'][1]),
        '@BE0@': cconf(N['BE0']), '@CHE@': cchain(N['che']),
        '@AI0@': cconf(N['AI0']), '@AI1@': cconf(N['AI1']),
        '@CHN@': cchain(N['chn']),
        '@CAN@': str(N['cn'][0]), '@CBN@': str(N['cn'][1]),
        '@BPAD@': str(N['bpad']), '@BFAR@': str(N['bfar']),
        '@BLEFT@': bleft, '@BFARE@': bfare, '@BWANT@': clist(bwant),
        '@IFARCHG@': ('' if N['ifar'] == 0 else
                      '  change (%s) with (%s).\n  rewrite !lift_app_blank.\n'
                      % (ifarb, ifarnest)),
        # [visx_]/[gen_] use LapCertGlueLift's bridges whether or not the
        # OUTER interior lap took the lift route, so it is imported here when
        # @GLUELIFT@ did not already do it.
        '@NESTIMPORT@': (('' if D.get('islack') else ' LapCertGlueLift')
                         + ' IXPGadgets NestedLap NestedLapLift'
                         + ('' if din['mod'] == ENCDATA[D['enc']]['mod']
                            else ' ' + din['mod'])),
        '@NVAL@': N['nval'],
        '@LAPIL@': (
            'exact lapi_@ID@.' if D.get('islack') else
            'intros p j q0 E. destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hr).\n'
            '  exists n, (Cc (Pos.succ p)).\n'
            '  split; [exact Hn | split; [exact Hr | reflexivity]].'),
        '@VISX@': (NEST_VISX + '\n\n' if D.get('visx') else ''),
    }
