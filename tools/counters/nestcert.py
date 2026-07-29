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
    'no shift chain': 3,
    'no second exit chain': 4,
    'boot of zero length at j=0': 5,
    'inner lap of zero length at i=0': 5,
}

# How many families ONE overflow phase may chain through beyond the first.
# WAVE18 section 4c found the SECOND count ("count 8->15, shift, count 8->15
# again"); the wave-22 residue track measured that the 13 machines left on
# "no shift chain"/"no second exit chain" carry a THIRD (and sometimes a
# fourth) count in yet another shifted frame.  [NestedLap2.boot_via_fill] is
# generic in (Cc, Cin1, Cin2), so it composes with itself and each extra
# count is one more application -- no new Coq.
MAXCOUNTS = 4

# Highest octave shift the inner-family search reports (families at
# [pow2 (j+oct)] for oct = 0..MAXOCT).  Octave-UP counts are representable
# ([b] = oct); offsets are not (the index-shift trap, 0/12).
MAXOCT = 2


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


def families(mid, ENCDATA, ENCS, K=6, maxtail=MAXTAIL, maxoct=MAXOCT):
    """Every (alphabet, state, tail, far, oct) in [mid] whose decoded values
    run exactly 2^(K-1+oct) .. 2^(K+oct)-1.

    [oct] is the family's OCTAVE SHIFT against the outer index: Stage A
    (NESTED_LAP_PLAN) measured 21% of inner counters running at another
    octave or offset, and the glue used to hard-wire [oct] = 0.  An
    octave-UP family starts at [pow2 (j+oct)], whose block count [j+oct] IS
    an sside ([a]=1, [b]=oct) -- unlike the offset form [pow2 j + 1], whose
    count [j-1] is not and measured 0/12 (the index-shift trap).

    Returned MOST-HITS-FIRST within each octave, [oct] = 0 first, but the
    caller must ENUMERATE: the best-scoring key is measured never to be the
    one the boot lands on.

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
    keys = []
    for o in range(maxoct + 1):
        want_run = list(range(2 ** (K - 1 + o), 2 ** (K + o)))
        oct_keys = [(k + (o,), len(v)) for k, v in hits.items()
                    if v == want_run]
        oct_keys.sort(key=lambda kv: -kv[1])
        keys += [k for k, _ in oct_keys]
    return keys


def split_at_fill(mid, ENC, key, K=6):
    """[mid] after the FIRST configuration at which [key]'s counter is all
    ones -- i.e. the part of the phase the exit chain has to cross.

    WAVE18 section 4c: on the machines whose exit measures EXPONENTIAL this
    half carries a SECOND consecutive family, at the same state and alphabet
    with a shifted tail.  That is the sync-bouncer shape, "count 8->15, shift,
    count 8->15 again".
    """
    name_in, st_in, ti, fi, oct_ = key
    w = LC.rstrip0(tuple(ENC[name_in](2 ** (K + oct_) - 1)) + tuple(ti))
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

      inner start  CinS = rep uD_in (j+o) ++ soD_in ++ tail_in  ( = E_in (pow2 (j+o)))
      inner fill   CinF = rep uS_in (j+o) ++ soS_in ++ tail_in  ( = E_in (fill _))
      inner lap    AI0  = rep uS_in i ++ sS_in   / AI1 = rep uD_in i ++ sD_in

    The family's octave shift [o] appears as the CONSTANT part of the count
    ([a] = 1, [b] = o), which is exactly what an sside can carry.
    """
    name_in, st_in, tail_in, far_in, oct_ = key
    din = ENCDATA[name_in]
    Fin = (tuple(far_in), (), 0, 0, ())
    ti = tuple(tail_in)
    CinS = (st_in, ((), din['uD'], 1, oct_, din['soD'] + ti), 0, Fin)
    CinF = (st_in, ((), din['uS'], 1, oct_, din['soS'] + ti), 0, Fin)
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


def _land(conf, st, d, post_want, far_want, what, oct_=0, pre_want=()):
    """A reached endpoint must be the anchor's syntactic shape plus TRAILING
    BLANKS on each side, and nothing else.  Returns (post pad, far pad)."""
    if conf[0] != st or conf[2] != 0:
        raise NestError('%s lands in the wrong state/head' % what)
    lpre, lu, la, lb, lpost = conf[1]
    if (tuple(lpre) != tuple(pre_want) or tuple(lu) != tuple(d)
            or (la, lb) != (1, oct_)):
        raise NestError('%s rep shape %r' % (what, (conf[1],)))
    pad = _slack(lpost, post_want, what + ' post')
    if conf[3][1]:
        raise NestError('%s far side carries a rep' % what)
    return pad, _slack(tuple(conf[3][0]) + tuple(conf[3][4]), far_want,
                       what + ' far')


def _inner_lap(tab, ENCDATA, key):
    """The inner family's own interior lap: chain, srun, landing pads."""
    name_in, st_in, tail_in, far_in, _oct = key
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
    name_in, st_in, tail_in, far_in, oct_ = key
    din, dout = ENCDATA[name_in], ENCDATA[enc]
    CinS, CinF, AI0, AI1 = endpoints(ENCDATA, enc, st0, tail, far, key)

    chb, _ = _chain(tab, True, True, B0, CinS)
    if chb is None:
        raise NestError('no boot chain')
    lap1 = _inner_lap(tab, ENCDATA, key)
    chn, rn = lap1['chn'], (None, lap1['cn'][0], lap1['cn'][1])

    more = []
    che, _ = _chain(tab, True, True, CinF, B1)
    if che is None:
        # WAVE18 section 4c: the exit is EXPONENTIAL because the phase runs a
        # SECOND count in a shifted frame -- and sometimes a third and a
        # fourth (wave-22).  Split at each fill and follow the chain of
        # families; [NestedLap2.boot_via_fill] folds each finished count into
        # the next one's boot, so no new composition theorem is needed.
        more, che = _more_counts(tab, ENCDATA, ENCS, ENC, CinF, B1, mid,
                                 key, K)
    BE0 = more[-1]['BE0'] if more else CinF
    rb = LC.srun(tab, True, True, chb, B0)
    re = LC.srun(tab, True, True, che, BE0)
    if rb is None or re is None:
        raise NestError('internal: srun disagrees with the search')
    if rb[2] == 0:
        raise NestError('boot of zero length at j=0')

    # The boot's landing shape: the inner anchor plus TRAILING BLANKS.
    BB1 = rb[0]
    bpad, bfar = _land(BB1, st_in, din['uD'],
                       tuple(din['soD']) + tuple(tail_in), tuple(far_in),
                       'boot', oct_)

    # The exit's landing shape is checked by [emit_lapcert.render]'s existing
    # [geo_] machinery (it is an ordinary overflow endpoint); all this needs
    # is how many blanks past the anchor's FAR side it stopped.
    if re[0][3][1]:
        raise NestError('exit far side carries a rep')
    efar = _slack(tuple(re[0][3][0]) + tuple(re[0][3][4]), tuple(far),
                  'exit far')

    d = dict(inner=name_in, st_in=st_in, tail_in=list(tail_in),
             far_in=list(far_in), oct=oct_,
             chb=chb, BB1=BB1, cb=(rb[1], rb[2]),
             che=che, BE0=BE0, BE1=re[0],
             ce=(re[1], re[2]),
             chn=lap1['chn'], AI0=lap1['AI0'], AI1=lap1['AI1'],
             cn=lap1['cn'],
             bpad=bpad, bfar=bfar, ipad=lap1['ipad'], ifar=lap1['ifar'],
             efar=efar, more=more)
    validate(tab, ENC, encf, enc, ENCDATA, st0, tail, far, key, d)
    return d


def _more_counts(tab, ENCDATA, ENCS, ENC, CinF, B1, mid, key, K,
                 maxkeys=40, maxcounts=MAXCOUNTS):
    """The chain of SHIFTs and further counts.  [CinF] is the current
    family's all-ones fill -- where the exit chain would have started and
    could not.  Returns ([level, ...], che): each level is one further family
    with the shift chain INTO it; [che] is the exit chain from the LAST
    level's fill.  Backtracks over candidate families at every level."""
    post = split_at_fill(mid, ENC, key, K)
    if not post:
        raise NestError('no exit chain')
    keys2 = families(post, ENCDATA, ENCS, K)
    keys2 = [k for k in keys2 if k != key]
    if not keys2:
        raise NestError('no exit chain')
    last = ['no shift chain']

    def go(CinFc, seg, used, depth):
        keysn = [k for k in families(seg, ENCDATA, ENCS, K) if k not in used]
        for k2 in keysn[:maxkeys]:
            name2, st2, ti2, fi2, oct2 = k2
            d2 = ENCDATA[name2]
            CinS2, CinF2, _, _ = endpoints(ENCDATA, None, None, (), (), k2)
            chm, _ = _chain(tab, True, True, CinFc, CinS2)
            if chm is None:
                _note(last, 'no shift chain')
                continue
            try:
                lap2 = _inner_lap(tab, ENCDATA, k2)
                rm = LC.srun(tab, True, True, chm, CinFc)
                if rm is None:
                    raise NestError('internal: srun disagrees with the search')
                mpad, mfar = _land(rm[0], st2, d2['uD'],
                                   tuple(d2['soD']) + tuple(ti2), tuple(fi2),
                                   'shift', oct2)
            except NestError as e:
                _note(last, str(e))
                continue
            lvl = dict(inner=name2, st_in=st2, tail_in=list(ti2),
                       far_in=list(fi2), oct=oct2,
                       chm=chm, BM0=CinFc, BM1=rm[0], cm=(rm[1], rm[2]),
                       # the pads of the chain INTO this family, named the
                       # same as the first family's so [_fam_reps] is shared
                       bpad=mpad, bfar=mfar, BE0=CinF2,
                       chn=lap2['chn'], AI0=lap2['AI0'], AI1=lap2['AI1'],
                       cn=lap2['cn'], ipad=lap2['ipad'], ifar=lap2['ifar'])
            che, _ = _chain(tab, True, True, CinF2, B1)
            if che is not None:
                return [lvl], che
            _note(last, 'no second exit chain')
            if depth + 1 < maxcounts:
                seg2 = split_at_fill(seg, ENC, k2, K)
                if seg2:
                    deeper = go(CinF2, seg2, used | {k2}, depth + 1)
                    if deeper is not None:
                        lvls, che = deeper
                        return [lvl] + lvls, che
        return None

    got = go(CinF, post, {key}, 1)
    if got is None:
        raise NestError(last[0])
    return got


def _note(last, msg):
    """Keep the FURTHEST failure for the report, by [_RANK]."""
    if _RANK.get(msg, len(_RANK)) >= _RANK.get(last[0], -1):
        last[0] = msg


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
    name_in, st_in, tail_in, far_in, oct_ = key
    tail, far = tuple(tail), tuple(far)
    ti, fi = tuple(tail_in), tuple(far_in)
    encin = ENC[name_in]
    n = 0
    more = d.get('more') or []

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
        v0, vf = 2 ** (j + oct_), 2 ** (j + oct_ + 1) - 1
        # boot
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st_in, tuple(encin(v0)) + ti, 0, fi)
        got = _sim(tab, start, d['cb'][0] * j + d['cb'][1])
        if not _eqlift(got, want):
            raise NestError('validate boot j=%d: %r want %r' % (j, got, want))
        # the first count
        laps(st_in, encin, ti, fi, d['cn'], v0, vf, 'inner')
        stc, encc, tc, fc, vfc = st_in, encin, ti, fi, vf
        for k, lvl in enumerate(more):
            # the SHIFT, then the next count
            enc2 = ENC[lvl['inner']]
            st2, ti2, fi2 = (lvl['st_in'], tuple(lvl['tail_in']),
                             tuple(lvl['far_in']))
            v02 = 2 ** (j + lvl['oct'])
            vf2 = 2 ** (j + lvl['oct'] + 1) - 1
            start = (stc, tuple(encc(vfc)) + tc, 0, fc)
            want = (st2, tuple(enc2(v02)) + ti2, 0, fi2)
            got = _sim(tab, start, lvl['cm'][0] * j + lvl['cm'][1])
            if not _eqlift(got, want):
                raise NestError('validate shift%d j=%d: %r want %r'
                                % (k + 2, j, got, want))
            laps(st2, enc2, ti2, fi2, lvl['cn'], v02, vf2,
                 'inner%d' % (k + 2))
            stc, encc, tc, fc, vfc = st2, enc2, ti2, fi2, vf2
        estart = (stc, tuple(encc(vfc)) + tc, 0, fc)
        # exit
        want = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = _sim(tab, estart, d['ce'][0] * j + d['ce'][1])
        if not _eqlift(got, want):
            raise NestError('validate exit j=%d: %r want %r' % (j, got, want))
        n += 1
    nc = 1 + len(more)
    d['nval'] = '%d overflow phases, j = %d..%d (%d inner laps%s)' % (
        n, jlo, jhi,
        sum(2 ** j - 1 for j in range(jlo, jhi + 1)) * nc,
        ', %d counts each' % nc if more else '')




# --------------------------------------------------------- family templates ---
#
# A nested board carries ONE or MORE inner families (WAVE18 section 4c found
# the second; wave-22 found chains of three and four).  Everything that is
# per-family -- the anchor, its [pow2] lemma, its own interior lap and that
# lap's two glue lemmas -- is emitted from these, once per family, with @S@
# the family suffix ('', '2', '3', ...).

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
    nif = N.get('ifar', 0)
    ifarb = clist(tuple(fi) + (0,) * nif)
    ifarnest = ('(' * nif + clist(fi)
                + ''.join(') ++ [S0]' for _ in range(nif)))
    return {
        '@S@': suffix, '@ORD@': ordinal,
        '@ENCI@': din.get('fn', N['inner']),
        '@ENCMODI@': din['mod'], '@SOMEI@': din['some'], '@NONEI@': din['none'],
        '@STI@': ST[N['st_in']], '@TAILI@': clist(ti), '@FARI@': clist(fi),
        '@USI@': clist(din['uS']), '@UDI@': clist(din['uD']),
        '@SDI@': clist(din['sD']), '@SODI@': clist(din['soD']),
        '@AI0@': cconf(N['AI0']) if 'AI0' in N else '',
        '@AI1@': cconf(N['AI1']) if 'AI1' in N else '',
        '@CHN@': cchain(N['chn']) if 'chn' in N else '',
        '@CAN@': str(N['cn'][0]) if 'cn' in N else '',
        '@CBN@': str(N['cn'][1]) if 'cn' in N else '',
        '@BPAD@': str(pad), '@BFAR@': str(farpad),
        '@BLEFT@': bleft, '@BFARE@': bfare, '@BWANT@': clist(bwant),
        '@LANDC@': landc, '@FILLC@': fillc,
        '@IFARCHG@': ('' if nif == 0 else
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
(** *** shift: count @F1@'s all-ones fill -> count @F@'s anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM@S2@0_@ID@ : sconf := @BM0@.
Definition BM@S2@1_@ID@ : sconf := @BM1@.
Definition chm@S2@_@ID@ : list lstep := @CHM@.

Lemma run_shift@S2@_@ID@ : srun tm true true chm@S2@_@ID@ BM@S2@0_@ID@ = Some (BM@S2@1_@ID@, @CAM@, @CBM@).
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


def _boot_stack(more, indent):
    """The boot for a MULTI-count board: fold each finished count into the
    next one's boot with one [boot_via_fill] application per shift, as a
    sequence of [assert]s (HB1 into the first family, HBk into the k-th).
    [boot_via_fill] is generic in (Cc, Cin1, Cin2), so the applications
    compose with no new Coq.  Ends with the last assert proved; the CALLER
    appends what consumes HB<nf>."""
    ind = ' ' * indent
    nf = len(more) + 1
    L = ['assert (HB1 : exists n c, 0 < n /\\ csteps tm n (Cc p) = Some c',
         ind + '              /\\ lift c = lift (Cin (pow2 j))).',
         ind + '{ exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).',
         ind + '  split; [lia|]. split; [| exact (gbo_@ID@ j)].',
         ind + '  rewrite (gso_@ID@ p j E).',
         ind + '  exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@',
         ind + '           run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)). }']
    for i, lvl in enumerate(more):
        f = i + 2
        sp, sc, ss = _fsfx(f - 1), _fsfx(f), _ssfx(f)
        ca, cb = lvl['cm']
        L += ['%sassert (HB%d : exists n c, 0 < n /\\ csteps tm n (Cc p) = Some c'
              % (ind, f),
              ind + '              /\\ lift c = lift (Cin%s (pow2 j))).' % sc,
              ind + '{ apply (boot_via_fill tm Cc Cin%s Cin%s lapin%s_@ID@ p (pow2 j) (pow2 j));'
              % (sp, sc, sp),
              ind + '    [exact HB%d|].' % (f - 1),
              ind + '  exists (%d * j + %d), (cden [] [] j BM%s1_@ID@).' % (ca, cb, ss),
              ind + '  split; [| exact (gbo%s_@ID@ j)].' % sc,
              ind + '  rewrite (gxi%s_@ID@ j).' % sp,
              ind + '  exact (srun_sound tm true true chm%s_@ID@ BM%s0_@ID@ BM%s1_@ID@ %d %d'
              % (ss, ss, ss, ca, cb),
              ind + '           run_shift%s_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)). }'
              % ss]
    return '\n'.join(L)


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


NEST_VISX_MULTI = r"""(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by the boot, the chained counts, and that prefix. *)
Lemma visx_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  @BOOTSTACK@
  destruct HB@NF@ as (nB & cB & _ & HcB & HlB).
  apply (vis_via_fill tm Cc Cin@LAST@ lapin@LAST@_@ID@ q p (pow2 j));
    [exists nB, cB; exact (conj HcB HlB)|].
  apply (vis_lift_of_csteps tm (fun _ : positive => Cin@LAST@ (fill (pow2 j))) xH).
  apply (vis_of_run tm (fun _ : positive => Cin@LAST@ (fill (pow2 j)))
                    true true l BE0_@ID@ xH j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gxi@LAST@_@ID@ j)].
Qed."""


NEST_OVFCASE = r"""  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_@ID@ p j' E)."""


_ORD = ['FIRST ', 'SECOND ', 'THIRD ', 'FOURTH ', 'FIFTH ']


def _fsfx(f):
    """FAMILY-name suffix: Cin/Cin2/Cin3..., lapin_/lapin2_/..."""
    return '' if f == 1 else str(f)


def _ssfx(f):
    """Suffix of the SHIFT into family [f]: chm_/BM0_/BM1_ kept bare for the
    second family (the wave-18 names), numbered from the third on."""
    return '' if f == 2 else str(f)


def _families(N):
    return [N] + (N.get('more') or [])


def nest_defs(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The DEFINITIONS block: one per family, then the chains."""
    N = D['nest']
    fams = _families(N)
    nf = len(fams)
    out = [_fill(FAM_DEFS,
                 _fam_reps(ENCDATA, F, clist, cconf, cchain, ST, _fsfx(i + 1),
                           _ORD[i] if nf > 1 else '', '', ''))
           for i, F in enumerate(fams)]
    shifts = []
    for i, lvl in enumerate(N.get('more') or []):
        f = i + 2
        shifts.append(_fill(SHIFT_DEF, {
            '@S2@': _ssfx(f), '@F@': str(f), '@F1@': str(f - 1),
            '@BM0@': cconf(lvl['BM0']), '@BM1@': cconf(lvl['BM1']),
            '@CHM@': cchain(lvl['chm']),
            '@CAM@': str(lvl['cm'][0]), '@CBM@': str(lvl['cm'][1])}))
    chains = NEST_CHAINS.replace('@SHIFTDEF@', ''.join(shifts))
    return '\n\n'.join(out) + '\n\n' + chains


def nest_glue(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The GLUE block: one per family, then [lapil_], [lapo_] and [visx_]."""
    N = D['nest']
    more = N.get('more') or []
    fams = _families(N)
    nf = len(fams)
    parts = []
    for i, F in enumerate(fams):
        f = i + 1
        landc = 'BB1_@ID@' if f == 1 else 'BM%s1_@ID@' % _ssfx(f)
        fillc = 'BE0_@ID@' if f == nf else 'BM%s0_@ID@' % _ssfx(f + 1)
        parts.append(_fill(FAM_GLUE,
                           _fam_reps(ENCDATA, F, clist, cconf, cchain, ST,
                                     _fsfx(f), '', landc, fillc)))
    out = '\n\n'.join(parts)
    out += '\n\n' + LAPIL
    boot = (BOOT1.strip() if not more
            else _boot_stack(more, 4) + '\n    exact HB%d.' % nf)
    out += '\n\n' + LAPO.replace('@BOOT@', boot).replace('@LAST@', _fsfx(nf))
    out += '\n\n@VISX@'
    return out


def nest_reps(D, ENCDATA, clist, cconf, cchain, ST, ID):
    """The machine-level holes the nested route adds (the per-family and
    per-shift ones are already substituted by [nest_defs] / [nest_glue])."""
    N = D['nest']
    more = N.get('more') or []
    nf = len(more) + 1
    mods = [ENCDATA[F['inner']]['mod'] for F in _families(N)]
    extra = ' '.join(sorted({m for m in mods
                             if m != ENCDATA[D['enc']]['mod']}))
    visx = ''
    if D.get('visx'):
        visx = (NEST_VISX if not more else
                NEST_VISX_MULTI
                .replace('@BOOTSTACK@', _boot_stack(more, 2))
                .replace('@NF@', str(nf))) + '\n\n'
    reps = {
        '@BB1@': cconf(N['BB1']), '@CHB@': cchain(N['chb']),
        '@CAB@': str(N['cb'][0]), '@CBB@': str(N['cb'][1]),
        '@BE0@': cconf(N['BE0']), '@CHE@': cchain(N['che']),
        # [visx_]/[gen_] use LapCertGlueLift's bridges whether or not the
        # OUTER interior lap took the lift route, so it is imported here when
        # @GLUELIFT@ did not already do it.
        '@NESTIMPORT@': (('' if D.get('islack') else ' LapCertGlueLift')
                         + ' IXPGadgets NestedLap NestedLapLift'
                         + (' NestedLap2' if more else '')
                         + ((' ' + extra) if extra else '')),
        '@NVAL@': N['nval'],
        '@LAPIL@': (
            'exact lapi_@ID@.' if D.get('islack') else
            'intros p j q0 E. destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hr).\n'
            '  exists n, (Cc (Pos.succ p)).\n'
            '  split; [exact Hn | split; [exact Hr | reflexivity]].'),
        '@VISX@': visx,
        '@LAST@': _fsfx(nf),
    }
    return reps


# ------------------------------------------------- the OFFSET family route ---
#
# Wave-22.  The dominant "no inner family at pow2 j" cluster's inner count
# runs 2^(j+1)+c .. 2^(j+2)-1 (c = 2 on every validated machine): the fill IS
# the all-ones the exit needs, but the START is offset, and
#
#     E (2^(j+1)+c) = blocks(c) ++ rep uD (j+1-cw) ++ soD      cw = bits(c)
#
# has block count j-1 at c = 2 -- unrepresentable in an sside indexed by j
# (the wave-15 index-shift trap).  The fix that MEASURES (22/162 validate) is
# to REINDEX the whole overflow branch at j = S j': every side is then an
# ordinary sside in j' (boot source b=1, inner start pre=blocks(c) b=0,
# fill b=2, outer successor b=2), and the j = 0 case (p = 1) is one CONCRETE
# run, handled the way the bootstrap lemma already handles concrete runs.
#
# [nested_overflow_lift] is stated at an arbitrary v0, so v0 = xO (xI (pow2
# j')) needs NO new composition theory; [fill (xO (xI (pow2 j'))) = fill
# (pow2 (S (S j')))] holds by cbn, so the fill glue reuses [cview_fill_pow2].

# The offset values the detector reports.  Only cw = 2 offsets (c = 2, 3)
# keep the reindex to ONE level; c = 1 is count j directly (no reindex, but
# 0 measured); deeper c would need a deeper split (0 measured).
OFFSETS = (2, 3)


def _blocks_of(c, A, B):
    """LSB-first digit blocks of ALL of [c]'s binary digits -- [c]'s own
    leading 1 becomes a B block; the zeros above it are the rep."""
    out = []
    while c >= 1:
        out += list(A if c % 2 == 0 else B)
        c //= 2
    return tuple(out)


def _v0term(c, var):
    """The Coq positive [2^(j+2)+c] as constructors over [pow2 var].  The
    OUTERMOST constructor is the LSB, so wrap in reverse bit order."""
    bits = []
    while c >= 1:
        bits.append(c % 2)
        c //= 2
    t = 'pow2 %s' % var
    for b in reversed(bits):
        t = '%s (%s)' % ('xI' if b else 'xO', t)
    return t


def _gather(mid, ENCDATA, ENCS, maxtail=MAXTAIL):
    """The decoded-value streams behind [families], keyed the same way."""
    hits = {}
    for (q, l, r) in mid:
        for name in ENCS:
            d = ENCDATA[name]
            if d['obS'] != 0:
                continue
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(maxtail + 1):
                if k > len(l) - 1:
                    break
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = decode(head, A, B, C)
                if v is not None:
                    hits.setdefault((name, q, tl, r), []).append(v)
    return hits


def offset_families(mid, ENCDATA, ENCS, K=6, maxtail=MAXTAIL):
    """Keys whose decoded values END with the run 2^(K+1)+c .. 2^(K+2)-1 --
    the octave-up count with an offset start.  Returns (key4, c) pairs."""
    out = []
    for key, vals in _gather(mid, ENCDATA, ENCS, maxtail).items():
        for c in OFFSETS:
            want = list(range(2 ** (K + 1) + c, 2 ** (K + 2)))
            if len(vals) >= len(want) and vals[-len(want):] == want:
                out.append((key, c))
    return out


_BOOKKEEP = ('SFoldL', 'SFoldR', 'SRotL', 'SRotR', 'SUnrotL', 'SUnrotR')


def _reland(tab, chain, start, target):
    """Rotate a chain's landing onto [target]'s EXACT syntactic shape.

    A chain accepted up to [lift] often lands on a denotational variant --
    e.g. one unit over-folded into the count ([b]+1, post shortened), which
    the offset glue's [replace]-based [cden] normalization cannot absorb.
    The fix is chain surgery, not glue surgery: bookkeeping steps (folds and
    rotations) cost (0,0), so strip them off the tail one at a time and ask
    [_shape_to] for an exact-shape rotation path from each stripped landing.
    Returns the fixed chain, or None."""
    base = list(chain)
    while True:
        r = LC.srun(tab, True, True, base, start)
        if r is None:
            return None
        c = r[0]
        if LC._match(c, target, True, True, True):
            fix = LC._shape_to(c, target, True, True, 8, False)
            if fix is not None:
                cand = base + fix
                if LC.srun(tab, True, True, cand, start) is not None:
                    return cand
        if base and base[-1][0] in _BOOKKEEP:
            base.pop()
        else:
            return None


def _sim_to_lift(tab, cfg, want, cap):
    """Steps until [cfg] reaches [want] up to trailing blanks; None if not."""
    for t in range(1, cap):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            return None
        if _eqlift(cfg, want):
            return t
    return None


def derive_offset(tab, ENCDATA, ENCS, ENC, enc, st0, tail, far, K=6):
    """The offset route: boot -> one offset count -> exit, reindexed at
    j = S j'.  Raises [NestError] if no offset family works."""
    dout = ENCDATA[enc]
    if dout['obS'] > 1:
        raise NestError('offset: outer obS > 1 is not wired')
    encf = ENC[enc]
    mid = phase_mid(tab, st0, encf, tail, far, K + 1)
    cands = offset_families(mid, ENCDATA, ENCS, K)
    if not cands:
        raise NestError('no inner family at pow2 j')
    tail_t, far_t = tuple(tail), tuple(far)
    F = (far_t, (), 0, 0, ())
    last = ['no inner family at pow2 j']
    for (key4, c) in cands:
        name_in, st_in, ti, fi = key4
        din = ENCDATA[name_in]
        preb = _blocks_of(c, tuple(din['uD']), tuple(din['uS']))
        Fin = (tuple(fi), (), 0, 0, ())
        ti_t = tuple(ti)
        if dout['obS'] >= 1:
            # peeled: one unit in the prefix, count j'+1 in total
            B0R = (st0, (dout['uS'], dout['uS'], 1, 1,
                         dout['soS'] + tail_t), 0, F)
        else:
            B0R = (st0, ((), dout['uS'], 1, 1, dout['soS'] + tail_t), 0, F)
        B1R = (st0, ((), dout['uD'], 1, 2, dout['soD'] + tail_t), 0, F)
        CinS = (st_in, (preb, din['uD'], 1, 0, din['soD'] + ti_t), 0, Fin)
        CinF = (st_in, ((), din['uS'], 1, 2, din['soS'] + ti_t), 0, Fin)
        try:
            chb, _ = _chain(tab, True, True, B0R, CinS)
            if chb is None:
                raise NestError('no boot chain')
            chb = _reland(tab, chb, B0R, CinS) or chb
            try:
                lap1 = _inner_lap(tab, ENCDATA, key4 + (0,))
                lap1['lmode'] = 'one'
            except NestError:
                lap1 = _inner_lap_split(tab, ENCDATA, key4 + (0,))
            refill = False
            che, _ = _chain(tab, True, True, CinF, B1R)
            if che is None:
                CinF = _refill(st_in, din, ti, fi)
                refill = True
                che, _ = _chain(tab, True, True, CinF, B1R)
            if che is None:
                raise NestError('no exit chain')
            che = _reland(tab, che, CinF, B1R) or che
            rb = LC.srun(tab, True, True, chb, B0R)
            re = LC.srun(tab, True, True, che, CinF)
            if rb is None or re is None:
                raise NestError('internal: srun disagrees with the search')
            if rb[2] == 0:
                raise NestError('boot of zero length at j=0')
            # the boot landing may carry EXTRA units folded into its count
            # (b inherited from B0R) and may arrive in the SHIFT1 form;
            # [gbo_]'s rep_add (+ rrc) normalization absorbs both
            bkind, lb_, bpad, bfar, u_l, pre_l = _land_offset(
                rb[0], st_in, din, tuple(din['soD']) + ti_t, tuple(fi), preb)
            # the exit landing: geo_'s HD wants the plain successor shape
            lpre, lu, la, lb, _ = re[0][1]
            if lpre or tuple(lu) != tuple(dout['uD']) or (la, lb) != (1, 2):
                raise NestError('exit landing rep shape %r' % (re[0][1],))
            if re[0][3][1]:
                raise NestError('exit far side carries a rep')
            efar = _slack(tuple(re[0][3][0]) + tuple(re[0][3][4]), far_t,
                          'exit far')
            # the j = 0 concrete lap: Cc 1 -> Cc 2 up to lift
            c1 = (st0, tuple(encf(1)) + tail_t, 0, far_t)
            n0 = _sim_to_lift(tab, c1,
                              (st0, tuple(encf(2)) + tail_t, 0, far_t), 20000)
            if n0 is None:
                raise NestError('offset: no concrete lap at p=1')
            # per-state first-visit witnesses from Cc 1, for the j=0 branch
            # of the visit bullets
            visz, cfg = {}, c1
            visz[c1[0]] = 0
            for t in range(1, 5000):
                try:
                    cfg = LC.wstep(tab, False, False, cfg)
                except LC.Halt:
                    break
                if cfg[0] not in visz:
                    visz[cfg[0]] = t
                if len(visz) == 4:
                    break
            d = dict(route='offset', c=c, preb=list(preb),
                     inner=name_in, st_in=st_in, tail_in=list(ti),
                     far_in=list(fi), oct=0,
                     chb=chb, BB1=rb[0], cb=(rb[1], rb[2]),
                     che=che, BE0=CinF, BE1=re[0], ce=(re[1], re[2]),
                     bpad=bpad, bfar=bfar, lb=lb_, bkind=bkind,
                     u_l=list(u_l), pre_l=list(pre_l),
                     efar=efar, more=[], refill=refill,
                     B0R=B0R, B1R=B1R, n0=n0, visz=visz,
                     lmode=lap1.get('lmode', 'one'))
            if d['lmode'] == 'one':
                d.update(chn=lap1['chn'], AI0=lap1['AI0'], AI1=lap1['AI1'],
                         cn=lap1['cn'], ipad=lap1['ipad'],
                         ifar=lap1['ifar'])
            else:
                d.update(AIZ0=lap1['AIZ0'], AIZ1=lap1['AIZ1'],
                         chnz=lap1['chnz'], cnz=lap1['cnz'],
                         AIP0=lap1['AIP0'], AIP1=lap1['AIP1'],
                         chnp=lap1['chnp'], cnp=lap1['cnp'],
                         ifarz=lap1['ifarz'], ifarp=lap1['ifarp'])
            validate_offset(tab, ENC, encf, enc, st0, tail, far, key4, c, d)
            return d
        except NestError as e:
            _note(last, str(e))
    raise NestError(last[0])


def validate_offset(tab, ENC, encf, enc, st0, tail, far, key4, c, d,
                    jlo=1, jhi=7):
    """Differential validation of the offset route: boot, every inner lap and
    the exit at j = jlo..jhi (index j' = j-1), plus the whole phase at
    j = 1, 2 and the concrete j = 0 lap."""
    name_in, st_in, tail_in, far_in = key4
    tail, far = tuple(tail), tuple(far)
    ti, fi = tuple(tail_in), tuple(far_in)
    encin = ENC[name_in]

    def lapcost(i):
        if d.get('lmode', 'one') == 'one':
            return d['cn'][0] * i + d['cn'][1]
        return (d['cnz'][1] if i == 0
                else d['cnp'][0] * (i - 1) + d['cnp'][1])

    def laps(v0, vf, j):
        for v in range(v0, vf):
            i, ov = carry(v)
            if ov:
                raise NestError('internal: inner overflow inside the run')
            a = (st_in, tuple(encin(v)) + ti, 0, fi)
            b = (st_in, tuple(encin(v + 1)) + ti, 0, fi)
            g = _sim(tab, a, lapcost(i))
            if not _eqlift(g, b):
                raise NestError('validate inner v=%d: %r want %r' % (v, g, b))

    for j in range(jlo, jhi + 1):
        jp = j - 1
        p = 2 ** (j + 1) - 1
        v0, vf = 2 ** (j + 1) + c, 2 ** (j + 2) - 1
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st_in, tuple(encin(v0)) + ti, 0, fi)
        got = _sim(tab, start, d['cb'][0] * jp + d['cb'][1])
        if not _eqlift(got, want):
            raise NestError('validate boot j=%d: %r want %r' % (j, got, want))
        laps(v0, vf, j)
        estart = (st_in, tuple(encin(vf)) + ti, 0, fi)
        ewant = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = _sim(tab, estart, d['ce'][0] * jp + d['ce'][1])
        if not _eqlift(got, ewant):
            raise NestError('validate exit j=%d: %r want %r' % (j, got, ewant))
    # the concrete j = 0 lap was found by simulation, so it holds by
    # construction; re-check it anyway
    c1 = (st0, tuple(encf(1)) + tail, 0, far)
    got = _sim(tab, c1, d['n0'])
    if not _eqlift(got, (st0, tuple(encf(2)) + tail, 0, far)):
        raise NestError('validate j=0 concrete lap')
    d['nval'] = ('offset c=%d: %d overflow phases, j = %d..%d '
                 '(%d inner laps), plus the concrete j=0 lap'
                 % (c, jhi - jlo + 1, jlo, jhi,
                    sum(2 ** (j + 1) - 1 - c for j in range(jlo, jhi + 1))))


# ------------------------------------------------ OFFSET route Coq emission ---

OFF_EPRE = r"""(** The OFFSET start: [E (2^(n+2)+@C@)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_@ID@ : forall n, @ENCI@ (@V0N@) = @PREBL@ ++ rep @UDI@ n ++ @SODI@.
Proof.
  intro n. cbn [@ENCI@]. rewrite epow2_@ID@.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed."""


OFF_CHAIN_GLUE = r"""(** The boot lands on the OFFSET inner anchor up to @BPAD@/@BFAR@ trailing
    blanks. *)
Lemma gbo_@ID@ : forall j, lift (cden [] [] j BB1_@ID@) = lift (Cin (@V0J@)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_@ID@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, BB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + @LB@) with (j + @LB@) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (@V0J@) = (@STI@, (@PREBL@ ++ rep @UDI@ j ++ @BWANT@, S0, @FARI@))).
  { unfold Cin_@ID@. rewrite epre_@ID@.
    first [ rewrite <- ?app_assoc; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The offset family's all-ones fill is the ordinary one two octaves up:
    [fill (@V0J@) = fill (pow2 (S (S j)))] by computation, so
    [cview_fill_pow2] still names the exit chain's start word. *)
Lemma gxi_@ID@ : forall j, Cin (fill (@V0J@)) = cden [] [] j BE0_@ID@.
Proof.
  intro j.
  assert (Hf : fill (@V0J@) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (@ENCMODI@.@NONEI@ (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_@ID@, cden, BE0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed."""


OFF_LAPO = r"""(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_@ID@ : exists n c', csteps tm n (Cc 1) = Some c'
    /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists @N0@.
  assert (H : match csteps tm @N0@ (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @N0@ (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** The outer OVERFLOW branch.  The offset family's block count is one short
    of the outer index, so the branch REINDEXES: the generic route runs at
    [j = S j'] and [j = 0] is the concrete lap above. *)
Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_@ID@.
  - apply (nested_overflow_lift tm Cc Cin lapin_@ID@ p (@V0JP@)).
    + exists (@CAB@ * j' + @CBB@), (cden [] [] j' BB1_@ID@).
      split; [lia|]. split; [| exact (gbo_@ID@ j')].
      rewrite (gso_@ID@ p j' E).
      exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
               run_boot_@ID@ [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (@CAO@ * j' + @CBO@), (cden [] [] j' B1_@ID@).
      split; [| exact (geo_@ID@ p j' E)].
      rewrite (gxi_@ID@ j').
      exact (srun_sound tm true true che_@ID@ BE0_@ID@ B1_@ID@ @CAO@ @CBO@
               run_exit_@ID@ [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed."""


OFF_VISX = r"""(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by boot + the inner counter's own laps + that prefix -- at the
    REINDEXED anchor (the caller destructs the outer index). *)
Lemma visx_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_@ID@ = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  apply (vis_via_fill tm Cc Cin lapin_@ID@ q p (@V0J@)).
  - exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@). split;
      [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j E).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - apply (vis_lift_of_csteps tm (fun _ : positive => Cin (fill (@V0J@))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin (fill (@V0J@)))
                      true true l BE0_@ID@ xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi_@ID@ j)].
Qed."""


VISZ = r"""(** State @STQ@'s visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_@STQ@_@ID@ : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = @STQ@.
Proof. exists @KQ@. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed."""


def _off_reps(N, clist, ID):
    """The offset-route holes shared by [OFF_EPRE]/[OFF_CHAIN_GLUE]."""
    preb = tuple(N['preb'])
    bwant = tuple(N['tail_in'])            # soD ++ tail_in is BWANT below
    return {
        '@C@': str(N['c']),
        '@V0N@': _v0term(N['c'], 'n'),
        '@V0J@': _v0term(N['c'], 'j'),
        '@PREBL@': clist(preb),
    }


def nest_defs_offset(D, ENCDATA, clist, cconf, cchain, ST, ID):
    N = D['nest']
    freps = _fam_reps(ENCDATA, N, clist, cconf, cchain, ST, '', '', '', '')
    fam_tpl = FAM_DEFS
    if N.get('lmode') == 'split':
        core = FAM_DEFS.split('(** Its own INTERIOR lap')[0].rstrip()
        lap = _fill(FAM_DEFS_LAP_SPLIT, {
            '@AIZ0@': cconf(N['AIZ0']), '@AIZ1@': cconf(N['AIZ1']),
            '@CHNZ@': cchain(N['chnz']),
            '@CAZN@': str(N['cnz'][0]), '@CBZN@': str(N['cnz'][1]),
            '@AIP0@': cconf(N['AIP0']), '@AIP1@': cconf(N['AIP1']),
            '@CHNP@': cchain(N['chnp']),
            '@CAPN@': str(N['cnp'][0]), '@CBPN@': str(N['cnp'][1])})
        fam_tpl = core + '\n\n' + lap
    fams = _fill(fam_tpl, freps)
    epre = _fill(_fill(OFF_EPRE, _off_reps(N, clist, ID)), freps)
    rrc = OFF_RRC if (N.get('bkind') == 'shift1' or N.get('refill')) else ''
    chains = NEST_CHAINS.replace('@SHIFTDEF@', '')
    return (fams + '\n\n' + epre + ('\n\n' + rrc if rrc else '')
            + '\n\n' + chains)


def nest_glue_offset(D, ENCDATA, clist, cconf, cchain, ST, ID):
    N = D['nest']
    freps = _fam_reps(ENCDATA, N, clist, cconf, cchain, ST, '', '', '', '')
    din = ENCDATA[N['inner']]
    fi = tuple(N['far_in'])
    if N.get('lmode') == 'split':
        ifz, ifp = N['ifarz'], N['ifarp']
        sreps = dict(freps)
        for (hole, nfar) in (('@IFZCHG@', ifz), ('@IFPCHG@', ifp)):
            fb = clist(fi + (0,) * nfar)
            fn = ('(' * nfar + clist(fi)
                  + ''.join(') ++ [S0]' for _ in range(nfar)))
            sreps[hole] = ('' if nfar == 0 else
                           '  change (%s) with (%s).\n'
                           '  rewrite !lift_app_blank.\n' % (fb, fn))
        sreps.update({'@CAZN@': str(N['cnz'][0]), '@CBZN@': str(N['cnz'][1]),
                      '@CAPN@': str(N['cnp'][0]),
                      '@CBPN@': str(N['cnp'][1])})
        out = _fill(FAM_GLUE_LAP_SPLIT, sreps)
    else:
        lap_part = FAM_GLUE.split('(** The chain into this family')[0].rstrip()
        out = _fill(lap_part, freps)
    # the chain glue: BLEFT carries the PRE blocks before the rep
    preb = tuple(N['preb'])
    ti = tuple(N['tail_in'])
    bwant = tuple(din['soD']) + ti
    pad, farpad = N['bpad'], N['bfar']
    u_l, pre_l = tuple(N['u_l']), tuple(N['pre_l'])
    shift1 = N.get('bkind') == 'shift1'
    lflat = ((preb[-1],) + bwant) if shift1 else bwant
    bleft = ('(' * pad + '%s ++ rep %s j ++ %s'
             % (clist(pre_l), clist(u_l), clist(lflat))
             + ''.join(') ++ [S0]' for _ in range(pad)))
    bfare = ('(' * farpad + clist(fi)
             + ''.join(') ++ [S0]' for _ in range(farpad)))
    creps = dict(_off_reps(N, clist, ID))
    creps.update({'@BLEFT@': bleft, '@BFARE@': bfare,
                  '@BWANT@': clist(bwant), '@LB@': str(N['lb'])})
    if shift1:
        creps.update({'@PRELC@': clist(pre_l), '@ULC@': clist(u_l),
                      '@XBWANT@': clist(lflat),
                      '@XC@': _sym(preb[-1]),
                      '@UTC@': clist(tuple(din['uD'])[:-1])})
        gbo = _fill(_fill(OFF_GBO_S1, creps), freps)
    else:
        gbo = _fill(_fill(OFF_CHAIN_GLUE.split('(** The offset family')[0]
                          .rstrip(), creps), freps)
    if N.get('refill'):
        uS = tuple(din['uS'])
        a, b = uS[0], uS[1] if len(uS) > 1 else uS[0]
        creps.update({'@BC@': _sym(b), '@UTFC@': '[%s]' % _sym(a)})
        gxi = _fill(_fill(OFF_GXI_RF, creps), freps)
    else:
        gxi = _fill(_fill('(** The offset family'
                          + OFF_CHAIN_GLUE.split('(** The offset family')[1],
                          creps), freps)
    out += '\n\n' + gbo + '\n\n' + gxi
    out += '\n\n' + LAPIL
    out += '\n\n' + _fill(OFF_LAPO, {'@V0JP@': _v0term(N['c'], "j'"),
                                     '@N0@': str(N['n0'])})
    out += '\n\n@VISX@'
    return out


def _sym(x):
    return 'S1' if x else 'S0'


def nest_reps_offset(D, ENCDATA, clist, cconf, cchain, ST, ID):
    N = D['nest']
    mods = [ENCDATA[N['inner']]['mod']]
    extra = ' '.join(sorted({m for m in mods
                             if m != ENCDATA[D['enc']]['mod']}))
    # p = 1 visit witnesses for every state the overflow bullets cover
    need = sorted(set(D.get('vis') or {}) | set(D.get('visx') or {}))
    visz = ''
    for q in need:
        if q not in N['visz']:
            raise RuntimeError('offset: no p=1 witness for state %d' % q)
        visz += _fill(VISZ, {'@STQ@': ST[q], '@KQ@': str(N['visz'][q])}) \
            + '\n\n'
    reps = {
        '@BB1@': cconf(N['BB1']), '@CHB@': cchain(N['chb']),
        '@CAB@': str(N['cb'][0]), '@CBB@': str(N['cb'][1]),
        '@BE0@': cconf(N['BE0']), '@CHE@': cchain(N['che']),
        '@NESTIMPORT@': (('' if D.get('islack') else ' LapCertGlueLift')
                         + ' IXPGadgets NestedLap NestedLapLift'
                         + ((' ' + extra) if extra else '')),
        '@NVAL@': N['nval'],
        '@LAPIL@': (
            'exact lapi_@ID@.' if D.get('islack') else
            'intros p j q0 E. destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hr).\n'
            '  exists n, (Cc (Pos.succ p)).\n'
            '  split; [exact Hn | split; [exact Hr | reflexivity]].'),
        '@VISX@': visz + ((_fill(OFF_VISX,
                                 {'@V0J@': _v0term(N['c'], 'j')}) + '\n\n')
                          if D.get('visx') else ''),
        '@LAST@': '',
    }
    return reps


# --------------------------------------- OFFSET route: split inner lap etc ---
#
# Wave-22b.  The Mp-outer cluster (74+ machines) has the SAME offset family
# as the boarded 22, but:
#   * the inner family's interior lap chain does not derive at the plain
#     AI0/AI1 endpoints -- the carry sweep's period sits one cell INTO the
#     unit, so SCycL only fires from the phase-shifted form.  The fix is the
#     interior-lap mirror of wave-13's j = 0 split: a Z chain at i = 0 and
#     peeled P chains at i = S i' (count i-1, one unit in the prefix);
#   * the exit chain does not derive from the plain fill form either; it
#     does from the REPHASED form (one cell of the unit rotated out front:
#     uS^(j+2) ++ soS = a :: (b,a)^(j+1) ++ b :: soS).
# Both are measured on the whole cluster: P=OK Z=OK exit2=OK on 80 machines.

def _inner_lap_split(tab, ENCDATA, key):
    """The inner interior lap in SPLIT form.  Mirrors the outer split
    (emit_lapcert.derive mode='split'): exact Z chain at i = 0, peeled P
    chains at i = S i'."""
    name_in, st_in, tail_in, far_in, _oct = key
    din = ENCDATA[name_in]
    Fin = (tuple(far_in), (), 0, 0, ())
    uS, uD = tuple(din['uS']), tuple(din['uD'])
    sS, sD = tuple(din['sS']), tuple(din['sD'])
    Z0 = (st_in, (sS, (), 0, 0, ()), 0, Fin)
    Z1 = (st_in, (sD, (), 0, 0, ()), 0, Fin)
    P0 = (st_in, (uS, uS, 1, 0, sS), 0, Fin)
    P1 = (st_in, (uD, uD, 1, 0, sD), 0, Fin)
    chz, _ = _chain(tab, False, True, Z0, Z1)
    chp, _ = _chain(tab, False, True, P0, P1)
    if chz is None or chp is None:
        raise NestError('no inner interior chain')
    rz = LC.srun(tab, False, True, chz, Z0)
    rp = LC.srun(tab, False, True, chp, P0)
    if rz is None or rp is None:
        raise NestError('internal: srun disagrees with the search')
    if rz[2] == 0 or rp[2] == 0:
        raise NestError('inner lap of zero length at i=0')
    # landings: left side exact (the opaque tail forces it); far may pad
    zpre, zu, za, zb, zpost = rz[0][1]
    if zu or (za, zb) != (0, 0) or tuple(zpre) + tuple(zpost) != sD:
        raise NestError('inner Z lap lands off shape %r' % (rz[0][1],))
    if rz[0][3][1]:
        raise NestError('inner Z far side carries a rep')
    ifarz = _slack(tuple(rz[0][3][0]) + tuple(rz[0][3][4]), tuple(far_in),
                   'inner Z far')
    ppad, ifarp = _land(rp[0], st_in, uD, sD, tuple(far_in),
                        'inner P lap', 0, uD)
    if ppad:
        raise NestError('inner P lap post pads (exact landing required)')
    return dict(lmode='split',
                AIZ0=Z0, AIZ1=rz[0], chnz=chz, cnz=(rz[1], rz[2]),
                AIP0=P0, AIP1=rp[0], chnp=chp, cnp=(rp[1], rp[2]),
                ifarz=ifarz, ifarp=ifarp)


def _land_offset(conf, st, din, bwant, far_want, preb):
    """Boot landing for the offset route: either the PLAIN shape
    (pre = preb, u = uD, any count constant [lb], flat residue = bwant), or
    the SHIFT1 shape (pre = preb minus its last cell x, u = x :: uD[:-1],
    flat residue = x :: bwant) -- the form the chain naturally lands in when
    the sweep's period sits one cell into the unit.  The glue bridges SHIFT1
    with one pinned [rep_rot] application ([rrc_]).

    Returns (kind, lb, pad, far_pad, u_l, pre_l)."""
    uD = tuple(din['uD'])
    if conf[0] != st or conf[2] != 0:
        raise NestError('boot lands in the wrong state/head')
    lpre, lu, la, lb, lpost = conf[1]
    if conf[3][1]:
        raise NestError('boot far side carries a rep')
    fpad = _slack(tuple(conf[3][0]) + tuple(conf[3][4]), far_want, 'boot far')
    if la != 1:
        raise NestError('boot rep shape %r' % (conf[1],))
    if tuple(lpre) == preb and tuple(lu) == uD:
        pad = _slack(uD * lb + tuple(lpost), bwant, 'boot post')
        return ('plain', lb, pad, fpad, uD, preb)
    x = preb[-1] if preb else None
    u_l = (x,) + uD[:-1] if preb else None
    if (preb and uD and uD[-1] == x and tuple(lpre) == preb[:-1]
            and tuple(lu) == u_l):
        pad = _slack(u_l * lb + tuple(lpost), (x,) + bwant, 'boot post')
        return ('shift1', lb, pad, fpad, u_l, preb[:-1])
    raise NestError('boot rep shape %r' % (conf[1],))


def _refill(st_in, din, tail_in, far_in):
    """The REPHASED fill start: one unit cell rotated out front.
    uS^(j+2) ++ soS ++ ti = a :: (b,a)^(j+1) ++ (b :: soS ++ ti)."""
    uS = tuple(din['uS'])
    a, b = uS[0], uS[1] if len(uS) > 1 else uS[0]
    return (st_in, ((a,), (b, a), 1, 1,
                    (b,) + tuple(din['soS']) + tuple(tail_in)), 0,
            (tuple(far_in), (), 0, 0, ()))


# ------------------------------------- OFFSET route: split/shift1 emission ---

OFF_RRC = r"""(** Rotating one fixed cell across a rep -- the bridge between a chain's
    natural landing frame and the encoding's block frame ([WTape.rep_rot],
    with the trailing cell fused into the tail). *)
Lemma rrc_@ID@ : forall (x : Sym) (u : list Sym) k (Y : list Sym),
  rep (x :: u) k ++ x :: Y = x :: rep (u ++ [x]) k ++ Y.
Proof.
  intros. change (x :: Y) with ([x] ++ Y). rewrite app_assoc, <- rep_rot.
  cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed."""


FAM_DEFS_LAP_SPLIT = r"""(** Its own INTERIOR lap, SPLIT: the carry sweep's period sits one cell
    into the unit, so i = 0 is one concrete window and i = S i' runs with a
    unit PEELED into the prefix (count i' = i - 1) -- the interior-lap
    mirror of the outer j = 0 split. *)
Definition AIZ@S@0_@ID@ : sconf := @AIZ0@.
Definition AIZ@S@1_@ID@ : sconf := @AIZ1@.
Definition chnz@S@_@ID@ : list lstep := @CHNZ@.

Lemma run_innerz@S@_@ID@ : srun tm false true chnz@S@_@ID@ AIZ@S@0_@ID@ = Some (AIZ@S@1_@ID@, @CAZN@, @CBZN@).
Proof. vm_compute. reflexivity. Qed.

Definition AIP@S@0_@ID@ : sconf := @AIP0@.
Definition AIP@S@1_@ID@ : sconf := @AIP1@.
Definition chnp@S@_@ID@ : list lstep := @CHNP@.

Lemma run_innerp@S@_@ID@ : srun tm false true chnp@S@_@ID@ AIP@S@0_@ID@ = Some (AIP@S@1_@ID@, @CAPN@, @CBPN@).
Proof. vm_compute. reflexivity. Qed."""


FAM_GLUE_LAP_SPLIT = r"""Lemma gsnz@S@_@ID@ : forall v q0, cview v = (0%nat, Some q0) ->
  Cin@S@ v = cden (@ENCI@ q0 ++ @TAILI@) [] 0 AIZ@S@0_@ID@.
Proof.
  intros v q0 E. destruct (@ENCMODI@.@SOMEI@ v 0 q0 E) as (H1 & _).
  unfold Cin@S@_@ID@, cden, AIZ@S@0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genz@S@_@ID@ : forall v q0, cview v = (0%nat, Some q0) ->
  lift (cden (@ENCI@ q0 ++ @TAILI@) [] 0 AIZ@S@1_@ID@) = lift (Cin@S@ (Pos.succ v)).
Proof.
  intros v q0 E. destruct (@ENCMODI@.@SOMEI@ v 0 q0 E) as (_ & H2).
  unfold Cin@S@_@ID@, cden, AIZ@S@1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  cbn [rep app]. rewrite ?app_nil_r.
@IFZCHG@  rewrite H2. first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app];
          rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gsnp@S@_@ID@ : forall v i q0, cview v = (S i, Some q0) ->
  Cin@S@ v = cden (@ENCI@ q0 ++ @TAILI@) [] i AIP@S@0_@ID@.
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v (S i) q0 E) as (H1 & _).
  unfold Cin@S@_@ID@, cden, AIP@S@0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genp@S@_@ID@ : forall v i q0, cview v = (S i, Some q0) ->
  lift (cden (@ENCI@ q0 ++ @TAILI@) [] i AIP@S@1_@ID@) = lift (Cin@S@ (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (@ENCMODI@.@SOMEI@ v (S i) q0 E) as (_ & H2).
  unfold Cin@S@_@ID@, cden, AIP@S@1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
@IFPCHG@  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma lapin@S@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin@S@ v) = Some c'
               /\ lift c' = lift (Cin@S@ (Pos.succ v)).
Proof.
  intros v i q0 E. destruct i as [|i'].
  - exists (@CAZN@ * 0 + @CBZN@), (cden (@ENCI@ q0 ++ @TAILI@) [] 0 AIZ@S@1_@ID@).
    split; [lia|]. split; [| exact (genz@S@_@ID@ v q0 E)].
    rewrite (gsnz@S@_@ID@ v q0 E).
    exact (srun_sound tm false true chnz@S@_@ID@ AIZ@S@0_@ID@ AIZ@S@1_@ID@ @CAZN@ @CBZN@
             run_innerz@S@_@ID@ (@ENCI@ q0 ++ @TAILI@) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (@CAPN@ * i' + @CBPN@), (cden (@ENCI@ q0 ++ @TAILI@) [] i' AIP@S@1_@ID@).
    split; [lia|]. split; [| exact (genp@S@_@ID@ v i' q0 E)].
    rewrite (gsnp@S@_@ID@ v i' q0 E).
    exact (srun_sound tm false true chnp@S@_@ID@ AIP@S@0_@ID@ AIP@S@1_@ID@ @CAPN@ @CBPN@
             run_innerp@S@_@ID@ (@ENCI@ q0 ++ @TAILI@) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed."""


OFF_GBO_S1 = r"""(** The boot lands in the SHIFT1 frame (the unit rotated one cell against
    the block frame), up to @BPAD@/@BFAR@ trailing blanks; [rrc_] bridges. *)
Lemma gbo_@ID@ : forall j, lift (cden [] [] j BB1_@ID@) = lift (Cin (@V0J@)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_@ID@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, BB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + @LB@) with (j + @LB@) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (@V0J@) = (@STI@, (@PRELC@ ++ rep @ULC@ j ++ @XBWANT@, S0, @FARI@))).
  { unfold Cin_@ID@. rewrite epre_@ID@.
    cbn [app]. rewrite <- ?app_assoc. cbn [app].
    rewrite (rrc_@ID@ @XC@ @UTC@ j).
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed."""


OFF_GXI_RF = r"""(** The exit chain starts from the REPHASED fill (one unit cell rotated out
    front); [rrc_] bridges it back to the encoding's block frame. *)
Lemma gxi_@ID@ : forall j, Cin (fill (@V0J@)) = cden [] [] j BE0_@ID@.
Proof.
  intro j.
  assert (Hf : fill (@V0J@) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (@ENCMODI@.@NONEI@ (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_@ID@, cden, BE0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite (rrc_@ID@ @BC@ @UTFC@ (S j)).
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed."""


# ============================================================== the CASCADE ---
#
# Wave-24.  `docs/CASCADE_EXIT.md` measured that one overflow phase of the
# 72-machine exp-counter bucket ("no exit chain" + "no boot chain") is a
# DESCENDING-OCTAVE CASCADE:
#
#     main count          2^j .. 2^(j+1)-1              tail T0
#     level l = j-1 .. 0  TWO counts 2^l .. 2^(l+1)-1, tails growing by one
#                         unit per level
#     closing sweep       -> the outer successor
#
# The step cost is Theta(2^j) -- WAVE18 section 4b's exponential, confirmed --
# but the COUNT OF COUNTS is AFFINE in j, which is why the fixed-N route
# ([MAXCOUNTS]) measured 0 of 87 and why [families] never saw it (it searches
# octaves >= 0 only, and [MAXTAIL] caps tails at 3 where the cascade needs
# ~2j).  What DOES express it is a level INDUCTION whose per-level pieces are
# ordinary chains uniform in the level index, with the growing part of the
# tail OPAQUE -- exactly what an sside's [X] already is.
#
# This section is the ENDPOINT EXTRACTOR for that induction.  It lives HERE
# and not in a probe on purpose: the wave-23 reconnaissance measured two
# ad-hoc trace scripts disagreeing on blank-head numbering, so [phase_mid]'s
# configurations and its [rstrip0] convention have to be single-sourced.
# Every framing produced below is CHECKED against [phase_mid]'s own
# configurations, at every level down to 0, before a chain is derived.
#
# The four transitions, at level [l] with [m] tail units ([l + m = M], the
# phase's invariant):
#
#   ENTRY  main fill  -> A(j-1) start   one-off at index j, tails concrete
#   AB     A(l) fill  -> B(l) start     index l, tail opaque
#   BA     B(l) fill  -> A(l-1) start   index l-1, tail opaque
#   CLOSE  B(0) fill  -> outer successor one-off at index j; the sweep READS
#                                       the whole tail, so there it is a rep
#                                       and not an opaque region
#
# Two framing degrees of freedom decide whether a transition derives, and both
# are searched rather than guessed -- section 4c spent a session on the first
# framing tried:
#
#   * the PEEL [r]: how many unit copies sit in [post] instead of in the
#     count.  The B->A turnaround walks back out over cells it has just
#     written, and at [r] = 0 it runs out of them one step early -- the window
#     is then blocked and no chain exists.  One peeled unit is what its
#     turnaround needs.
#   * the SPLIT [P]: how many cells past the count stay concrete before the
#     opaque tail starts.  A->B never reads the growing region; B->A reads
#     exactly one cell into it (the unit misreads there, which is what ENDS
#     the eat), so its split cannot sit where A->B's does.

CASC_MAXTAIL = 64          # the cascade's tails are ~2j cells, not MAXTAIL
CASC_MINLEN = 4            # shortest count run [cascade_segments] reports
CASC_PEEL = 3              # unit copies the framing search may peel
CASC_POST = 14             # concrete cells past the count the search may keep


def _gather_idx(mid, ENCDATA, ENCS, maxtail=MAXTAIL, encs=None):
    """[_gather] with the phase POSITION kept: key -> [(mid index, value)].

    The cascade needs the positions.  Its counts are told apart from one
    another -- and from the octave SHADOWS, which decode over the same span as
    the count they shadow -- by WHERE in the phase they run, not by their key.
    """
    hits = {}
    for i, (q, l, r) in enumerate(mid):
        for name in (encs or ENCS):
            d = ENCDATA[name]
            if d['obS'] != 0:
                continue
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(maxtail + 1):
                if k > len(l) - 1:
                    break
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = decode(head, A, B, C)
                if v is not None:
                    hits.setdefault((name, q, tl, r), []).append((i, v))
    return hits


def cascade_segments(mid, ENCDATA, ENCS, maxtail=CASC_MAXTAIL,
                     minlen=CASC_MINLEN, encs=None):
    """Maximal consecutive-ascending count runs; the widest kept when one
    octave shadows another over the same span."""
    segs = []
    for key, iv in _gather_idx(mid, ENCDATA, ENCS, maxtail, encs).items():
        i0 = 0
        while i0 < len(iv):
            k = i0
            while k + 1 < len(iv) and iv[k + 1][1] == iv[k][1] + 1:
                k += 1
            if k - i0 + 1 >= minlen:
                segs.append((iv[i0][0], iv[k][0], iv[i0][1], iv[k][1], key))
            i0 = k + 1
    segs.sort()
    return [s for s in segs
            if not any(o[0] <= s[0] and s[1] <= o[1]
                       and (o[3] - o[2]) > (s[3] - s[2]) for o in segs)]


def cascade_runs(mid, ENCDATA, ENCS, maxtail=CASC_MAXTAIL,
                 minlen=CASC_MINLEN, encs=None, prefer=None):
    """The phase's counts as a NON-OVERLAPPING chain, earliest first.

    Non-overlap is what separates a real cascade level from an octave shadow:
    a shadow decodes over (nearly) the same span as the count it shadows, so
    an earliest-start greedy scan keeps the count and drops the shadow.

    [prefer] breaks the remaining tie.  Digit alphabets coincide -- `Jp` and
    the inferred `Alph_11_10_1` are the same three words -- and which name the
    scan reports decides which Coq module the board has to import, so the
    OUTER anchor's alphabet is preferred when it decodes the run too."""
    segs = sorted(cascade_segments(mid, ENCDATA, ENCS, maxtail, minlen, encs),
                  key=lambda s: (s[0], s[1], s[4][0] != prefer, s[4]))
    out, cur = [], -1
    for s in segs:
        if s[0] > cur:
            out.append(s)
            cur = s[1]
    return out


def _insert_ats(a, b, w):
    """Every [e] with [b] = [a] carrying [w] cells INSERTED at [e].

    The cascade's tails grow by one unit per level after a fixed head, and
    this reads the head length off two consecutive levels instead of assuming
    it.  There is usually more than one reading -- a tail `10101` growing to
    `1010101` admits both (head `[]`, unit `10`) and (head `[1]`, unit `01`)
    -- and only one of them makes the tail `head ++ rep unit m` for an [m]
    that descends with the level, so ALL of them are returned and the caller
    picks the one whose whole law closes."""
    if len(b) != len(a) + w:
        return []
    return [e for e in range(len(a) + 1)
            if a[:e] == b[:e] and a[e:] == b[e + w:]]


def _tail_mlaw(T, levels, ex, unit, w):
    """[M] with [T p = ex ++ rep unit (M - p)] at every measured level, or
    None."""
    M = None
    for p in levels:
        rest = T[p][len(ex):]
        if T[p][:len(ex)] != ex or len(rest) % w or \
                rest != unit * (len(rest) // w):
            return None
        m = len(rest) // w
        if M is None:
            M = m + p
        elif M != m + p:
            return None
    return M


def cascade_law(mid, ENCDATA, ENCS, K, encs=None, maxtail=CASC_MAXTAIL,
                prefer=None):
    """Read the cascade's LAW off one measured overflow phase.

    Returns the inner family, the main count's tail, and the tail law of the
    per-level counts: [tail_A l = extraA ++ rep unit (M - l)], likewise for the
    second count of the level.  Nothing about the unit, the head cells, the
    number of levels or [M] is assumed -- all four are measured, and a phase
    that does not obey the law raises rather than being forced into it."""
    j = K - 1
    runs = cascade_runs(mid, ENCDATA, ENCS, maxtail, encs=encs,
                        prefer=prefer)
    if len(runs) < 5:
        raise NestError('no cascade: %d counts in the phase' % len(runs))
    (_, _, v0, v1, key0) = runs[0]
    if (v0, v1) == (2 ** j, 2 ** (j + 1) - 1):
        oct_, big_in = 0, 0
        lev_runs = runs[1:]
    elif (v0, v1) == (2 ** (j - 1), 2 ** j - 1):
        # The whole cascade sits ONE OCTAVE DOWN: there is no separate main
        # count -- the top level (j-1) carries TWO counts like every other
        # level, and the boot lands on its FIRST count.  The overflow at
        # p = 1 (outer index 0) has no cascade at all and is a concrete lap.
        # These are wave-24's 12 "main count at 2^(j-1)..2^j-1" non-gated
        # rows; the level structure below them is the standard one.
        oct_ = -1
        # The phase does not end at level 0: after the descent these
        # machines run ONE WHOLE ASCENDING COUNT at octave j+1 (values
        # 2^(j+1)..2^(j+2)-1, a short constant tail) before settling on the
        # outer successor -- measured Theta(2^j), so the close is that
        # count's own laps between two affine chains (CLOSEA in, CLOSEB
        # out), not a sweep.  Separate it from the level runs here.
        lev_runs = [r for r in runs if r[2].bit_length() - 1 < j]
        # The closing count ends at the octave's fill, but it need not START
        # at the octave: on part of this bucket it ENTERS ONE VALUE IN, at
        # 2^(j+1)+1 = [xI (pow2 j)], because the chain into it lands on the
        # count's second value rather than its first.  Nothing else about the
        # phase changes -- the fill is the same value either way, so the way
        # OUT is untouched -- so read the entry offset off the run instead of
        # demanding it be zero.
        big, big_in = None, None
        for cand in (0, 1):
            hit = [r for r in runs
                   if (r[2], r[3]) == (2 ** (j + 1) + cand, 2 ** (j + 2) - 1)]
            if hit:
                big, big_in = hit, cand
                break
        if big is None:
            raise NestError('no cascade: octave-down phase has no closing '
                            'count at octave %d' % (j + 1))
    else:
        raise NestError('no cascade: main count is %d..%d' % (v0, v1))
    name, st, tail_main, far_in = key0
    big_tail = None
    if oct_ == -1:
        bkey = big[0][4]
        if (bkey[0], bkey[1], bkey[3]) != (name, st, far_in):
            raise NestError('no cascade: the closing count at %s@%d far=%r '
                            'leaves the family' % (bkey[0], bkey[1], bkey[3]))
        big_tail = bkey[2]
    lev = {}
    for (i0, i1, a, b, key) in lev_runs:
        if (key[0], key[1], key[3]) != (name, st, far_in):
            raise NestError('no cascade: a count at %s@%d far=%r leaves the '
                            'family' % (key[0], key[1], key[3]))
        p = a.bit_length() - 1
        if (a, b) != (2 ** p, 2 ** (p + 1) - 1):
            raise NestError('no cascade: count %d..%d is not an octave'
                            % (a, b))
        lev.setdefault(p, []).append(key[2])
    levels = sorted(lev, reverse=True)
    if levels[0] != j - 1:
        raise NestError('no cascade: top level is %d, not %d'
                        % (levels[0], j - 1))
    if levels != list(range(levels[0], levels[0] - len(levels), -1)):
        raise NestError('no cascade: levels %r are not consecutive' % levels)
    if len(levels) < 2:
        raise NestError('no cascade: one level only')
    for p in levels:
        if len(lev[p]) != 2:
            raise NestError('no cascade: level %d has %d counts, not two'
                            % (p, len(lev[p])))
    tA = {p: lev[p][0] for p in levels}
    tB = {p: lev[p][1] for p in levels}
    w = len(tA[levels[1]]) - len(tA[levels[0]])
    if w <= 0:
        raise NestError('no cascade: the tails do not grow (%d)' % w)
    opts = {}
    for nm, T in (('A', tA), ('B', tB)):
        cur = None
        for p in levels[:-1]:
            got = {(e, T[p - 1][e:e + w])
                   for e in _insert_ats(T[p], T[p - 1], w)}
            cur = got if cur is None else (cur & got)
        if not cur:
            raise NestError('no cascade: the %s tails do not grow by one fixed '
                            'unit' % nm)
        opts[nm] = sorted(cur)
    for (eA, unit) in opts['A']:
        exA = tA[levels[0]][:eA]
        MA = _tail_mlaw(tA, levels, exA, unit, w)
        if MA is None:
            continue
        for (eB, uB) in opts['B']:
            if uB != unit:
                continue
            exB = tB[levels[0]][:eB]
            if _tail_mlaw(tB, levels, exB, unit, w) != MA:
                continue
            # Is the MAIN count just the level-j second count?  On the
            # exemplar it is -- [tail_main] = extraB ++ rep unit (M - j) on
            # the nose -- and then the phase is uniform from level j down,
            # the boot lands on B(j), and the level induction needs no
            # separate entry step at all.
            return dict(inner=name, st_in=st, far_in=far_in,
                        tail_main=tail_main, unit=unit, extraA=exA,
                        extraB=exB, levels=levels, K=K, j=j, M=MA, oct=oct_,
                        big_tail=big_tail, big_in=big_in,
                        main_is_B=(oct_ == 0
                                   and tail_main == exB + unit * (MA - j)))
    raise NestError('no cascade: no tail law head ++ rep unit (M - l) fits '
                    'both counts')


def cascade_words(law, ENCDATA, l):
    """The four per-level words, in [phase_mid]'s left-side form."""
    d = ENCDATA[law['inner']]
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    soS, soD = tuple(d['soS']), tuple(d['soD'])
    T = law['unit'] * (law['M'] - l)
    tA, tB = law['extraA'] + T, law['extraB'] + T
    return dict(A0=uD * l + soD + tA, A1=uS * l + soS + tA,
                B0=uD * l + soD + tB, B1=uS * l + soS + tB)


def cascade_check(mid, law, ENCDATA):
    """Every level's four words -- PREDICTED by the law, then looked up among
    [phase_mid]'s own configurations, in phase order, down to level 0.

    This is the gate that the law describes the machine and not a hand-read
    trace.  The two lowest levels are never reported by [cascade_segments]
    (their runs are 2 and 1 values long, below [CASC_MINLEN]), so finding them
    here is a genuine extrapolation test, not a restatement of the input."""
    st, far = law['st_in'], tuple(law['far_in'])
    pos, out = -1, []
    for l in range(law['j'] - 1, -1, -1):
        w, found = cascade_words(law, ENCDATA, l), {}
        for nm in ('A0', 'A1', 'B0', 'B1'):
            # a level-0 count is one value wide, so its start IS its fill
            lo = pos + 1 if nm in ('A0', 'B0') else pos
            want = (st, LC.rstrip0(w[nm]), far)
            hit = next((i for i in range(lo, len(mid)) if mid[i] == want), None)
            if hit is None:
                raise NestError('cascade level %d: %s is not in the phase'
                                % (l, nm))
            found[nm] = hit
            pos = hit
        out.append((l, found))
    return out


# ------------------------------------------------------- the framing search ---

def _side(pre, u, c, i, r, tl, P):
    """One endpoint, framed: peel [r] unit copies out of the count into
    [post], then keep [P] cells concrete before the opaque tail.  Returns
    (sside, X), or None when the framing does not exist at this index."""
    if r < 0 or c - r < 0 or c - r < i:
        return None
    T = tuple(u) * r + tuple(tl)
    if P > len(T):
        return None
    return ((tuple(pre), tuple(u), 1, c - r - i, T[:P]), T[P:])


def _frame_pair(S, D, ns, peel=CASC_PEEL, post=CASC_POST):
    """Every (peel, split) framing of a transition that is UNIFORM IN THE
    INDEX: one sside per endpoint, the same at every sampled index, sharing
    one opaque tail.  [S]/[D] are (pre, u, count, tail) laws."""
    out = []
    for rs in range(peel + 1):
        for rd in range(peel + 1):
            if len({S['c'](n) - rs - (D['c'](n) - rd) for n in ns}) != 1:
                continue
            for P in range(post + 1):
                cand, Xs, ok = None, {}, True
                for n in ns:
                    i = min(S['c'](n) - rs, D['c'](n) - rd)
                    s = _side(S['pre'], S['u'], S['c'](n), i, rs, S['t'](n), P)
                    if s is None:
                        ok = False
                        break
                    Pd = len(tuple(D['u']) * rd + tuple(D['t'](n))) - len(s[1])
                    e = _side(D['pre'], D['u'], D['c'](n), i, rd, D['t'](n),
                              Pd) if Pd >= 0 else None
                    if e is None or e[1] != s[1]:
                        ok = False
                        break
                    if cand is None:
                        cand = (s[0], e[0], i - n)
                    elif cand != (s[0], e[0], i - n):
                        ok = False
                        break
                    Xs[n] = s[1]
                if ok and cand is not None:
                    out.append(dict(peel=(rs, rd), post=P, ssrc=cand[0],
                                    sdst=cand[1], ioff=cand[2], Xs=Xs))
    return out


def cascade_transitions(law, ENCDATA, enc, st0, tail, far):
    """The four transitions, each as a (pre, u, count, tail) law per endpoint
    plus the indices to sample.  [n] is the LEVEL for the per-level pair and
    the outer index [j] for the two one-offs."""
    d, dout = ENCDATA[law['inner']], ENCDATA[enc]
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    soS, soD = tuple(d['soS']), tuple(d['soD'])
    W, M, j = law['unit'], law['M'], law['j']
    eA, eB, tm = law['extraA'], law['extraB'], tuple(law['tail_main'])
    st, fi, tl, fr = law['st_in'], tuple(law['far_in']), tuple(tail), tuple(far)
    dm = M - j                              # tail units at level j; M = j + dm
    out = [
        dict(kind='ENTRY', ns=[j], sst=st, dst=st, sfar=fi, dfar=fi,
             S=dict(pre=(), u=uS, c=lambda n: n, t=lambda n: soS + tm),
             D=dict(pre=(), u=uD, c=lambda n: n - 1,
                    t=lambda n: soD + eA + W * (dm + 1))),
        dict(kind='AB', ns=law['levels'], sst=st, dst=st, sfar=fi, dfar=fi,
             S=dict(pre=(), u=uS, c=lambda n: n,
                    t=lambda n: soS + eA + W * (M - n)),
             D=dict(pre=(), u=uD, c=lambda n: n,
                    t=lambda n: soD + eB + W * (M - n))),
        dict(kind='BA', ns=[l for l in law['levels'] if l >= 1],
             sst=st, dst=st, sfar=fi, dfar=fi,
             S=dict(pre=(), u=uS, c=lambda n: n,
                    t=lambda n: soS + eB + W * (M - n)),
             D=dict(pre=(), u=uD, c=lambda n: n - 1,
                    t=lambda n: soD + eA + W * (M - n + 1))),
        dict(kind='CLOSE', ns=[j], sst=st, dst=st0, sfar=fi, dfar=fr,
             S=dict(pre=soS + eB, u=W, c=lambda n: n + dm, t=lambda n: ()),
             D=dict(pre=(), u=tuple(dout['uD']), c=lambda n: n + 1,
                    t=lambda n: tuple(dout['soD']) + tl)),
    ]
    if law.get('oct', 0) == -1:
        # the octave-down close: level-0 fill -> the octave-(j+1) closing
        # count's START (its exponentially many laps live in [fill_hop]) ->
        # from its FILL to the outer successor
        bt = tuple(law['big_tail'])
        # [big_in] = 1: the closing count is entered one value in, at
        # 2^(j+1)+1, whose word is uS ++ rep uD j ++ soD -- one FEWER unit
        # copy than the octave's own word, with the odd digit peeled into the
        # prefix.  The way out is unchanged: both values share a fill.
        bi = law.get('big_in', 0)
        out[-1:] = [
            dict(kind='CLOSEA', ns=[j], sst=st, dst=st, sfar=fi, dfar=fi,
                 S=dict(pre=soS + eB, u=W, c=lambda n: n + dm,
                        t=lambda n: ()),
                 D=dict(pre=() if not bi else uS, u=uD,
                        c=(lambda n: n + 1) if not bi else (lambda n: n),
                        t=lambda n: soD + bt)),
            dict(kind='CLOSEB', ns=[j], sst=st, dst=st0, sfar=fi, dfar=fr,
                 S=dict(pre=(), u=uS, c=lambda n: n + 1,
                        t=lambda n: soS + bt),
                 D=dict(pre=(), u=tuple(dout['uD']), c=lambda n: n + 1,
                        t=lambda n: tuple(dout['soD']) + tl)),
        ]
    return out


def cascade_endpoints(tab, ENCDATA, ENCS, ENC, enc, st0, tail, far, K=7,
                      encs=None):
    """The CASCADE route's endpoints and chains, gated.

    Reads the law off one measured overflow phase, checks it against
    [phase_mid]'s own configurations at every level down to 0, then derives:
    the BOOT into the main count, the inner family's own interior lap (shared
    by every level -- the tail is opaque to it), and the four transition
    chains.  Raises [NestError] with the piece that did not derive."""
    encf = ENC[enc]
    mid = phase_mid(tab, st0, encf, tail, far, K, maxT=4000000)
    law = cascade_law(mid, ENCDATA, ENCS, K, encs, prefer=enc)
    law['found'] = cascade_check(mid, law, ENCDATA)
    oct_ = law.get('oct', 0)
    if oct_ == 0:
        key = (law['inner'], law['st_in'], tuple(law['tail_main']),
               tuple(law['far_in']), 0)
    else:
        # one octave down: the boot lands on the TOP level's FIRST count,
        # A(j-1) at value 2^(j-1), whose tail carries dm+1 units
        key = (law['inner'], law['st_in'],
               tuple(law['extraA'])
               + tuple(law['unit']) * (law['M'] - law['j'] + 1),
               tuple(law['far_in']), 0)
    CinS, CinF, _, _ = endpoints(ENCDATA, enc, st0, tail, far, key)
    B0, B1 = _confs_ovf(ENCDATA, enc, st0, tail, far)
    if oct_ == -1:
        # the boot chain runs at the REINDEXED anchor (one below the outer
        # index), so its source carries one peeled unit copy in the prefix
        dout = ENCDATA[enc]
        B0 = (st0, (dout['uS'], dout['uS'], 1, dout['obS'],
                    tuple(dout['soS']) + tuple(tail)), 0,
              (tuple(far), (), 0, 0, ()))
    chb, _ = _chain(tab, True, True, B0, CinS)
    if chb is None:
        raise NestError('no boot chain')
    rb = LC.srun(tab, True, True, chb, B0)
    if rb is None:
        raise NestError('internal: srun disagrees with the search')
    lap = _inner_lap(tab, ENCDATA, key)
    trans = {}
    for tr in cascade_transitions(law, ENCDATA, enc, st0, tail, far):
        if oct_ == -1 and tr['kind'] == 'ENTRY':
            # no main count to enter from: the boot IS the entry
            continue
        got = None
        for fr in _frame_pair(tr['S'], tr['D'], tr['ns']):
            el = not any(fr['Xs'].values())
            src = (tr['sst'], fr['ssrc'], 0, (tr['sfar'], (), 0, 0, ()))
            dst = (tr['dst'], fr['sdst'], 0, (tr['dfar'], (), 0, 0, ()))
            ch, lift = _chain(tab, el, True, src, dst)
            if ch is None:
                continue
            r = LC.srun(tab, el, True, ch, src)
            if r is None:
                continue
            got = dict(fr, chain=ch, lift=lift, el=el, src=src, dst=dst,
                       land=r[0], cost=(r[1], r[2]))
            break
        if got is None:
            raise NestError('no cascade %s chain' % tr['kind'])
        trans[tr['kind']] = got
    d = dict(law=law, key=key, trans=trans, chb=chb, BB1=rb[0],
             cb=(rb[1], rb[2]), B0=B0, B1=B1, CinS=CinS, CinF=CinF,
             chn=lap['chn'], AI0=lap['AI0'], AI1=lap['AI1'],
             cn=lap['cn'], ipad=lap['ipad'], ifar=lap['ifar'])
    if oct_ == -1:
        # the outer index 0 overflow (p = 1) has no cascade: a concrete lap,
        # plus per-state first-visit witnesses for the j = 0 visit bullets
        # (the offset route's exact device)
        tail_t, far_t = tuple(tail), tuple(far)
        c1 = (st0, tuple(encf(1)) + tail_t, 0, far_t)
        n0 = _sim_to_lift(tab, c1,
                          (st0, tuple(encf(2)) + tail_t, 0, far_t), 20000)
        if n0 is None:
            raise NestError('cascade: no concrete lap at p=1')
        visz, cfg = {c1[0]: 0}, c1
        for t in range(1, 5000):
            try:
                cfg = LC.wstep(tab, False, False, cfg)
            except LC.Halt:
                break
            if cfg[0] not in visz:
                visz[cfg[0]] = t
            if len(visz) == 4:
                break
        d['n0'], d['visz'] = n0, visz
    return d


def cascade_validate(tab, ENC, ENCDATA, enc, st0, tail, far, d,
                     jlo=2, jhi=7):
    """Differentially check the WHOLE cascade against the raw simulator: the
    boot, every count of every level, and all three transition chains, at
    exact step counts and exact configurations, over a range of outer indices.

    This is wave-18's discipline unchanged, and for this route it is the load-
    bearing one: the chains are derived at ONE index from ONE phase, and only
    a replay at other indices distinguishes a level-uniform chain from a
    coincidence at the index it was read off."""
    law = d['law']
    encin, encf = ENC[law['inner']], ENC[enc]
    st, fi = law['st_in'], tuple(law['far_in'])
    W, dm = law['unit'], law['M'] - law['j']
    eA, eB = law['extraA'], law['extraB']
    tail, far = tuple(tail), tuple(far)
    cn, cb = d['cn'], d['cb']
    cBA = d['trans']['BA']['cost'], d['trans']['BA']['ioff']
    cAB = d['trans']['AB']['cost'], d['trans']['AB']['ioff']
    if 'CLOSE' in d['trans']:
        cCL = d['trans']['CLOSE']['cost'], d['trans']['CLOSE']['ioff']
    else:
        cCA = d['trans']['CLOSEA']['cost'], d['trans']['CLOSEA']['ioff']
        cCB = d['trans']['CLOSEB']['cost'], d['trans']['CLOSEB']['ioff']

    def tl(ex, l, j):
        return ex + W * (j + dm - l)

    def hop(a, b, cost, n, what):
        got = _sim(tab, a, cost[0][0] * (n + cost[1]) + cost[0][1])
        if not _eqlift(got, b):
            raise NestError('validate %s: %r want %r' % (what, got, b))

    def laps(t, v0, vf, what):
        for v in range(v0, vf):
            i, ov = carry(v)
            if ov:
                raise NestError('internal: inner overflow inside the run')
            a = (st, tuple(encin(v)) + t, 0, fi)
            b = (st, tuple(encin(v + 1)) + t, 0, fi)
            g = _sim(tab, a, cn[0] * i + cn[1])
            if not _eqlift(g, b):
                raise NestError('validate %s v=%d: %r want %r'
                                % (what, v, g, b))

    oct_ = law.get('oct', 0)
    nlap = 0
    if oct_ == -1:
        # the concrete p = 1 lap first, then the generic branch from j = 1:
        # boot lands on A(j-1)'s START, one AB hop enters the descent, and
        # the level structure below is the standard one
        got = _sim(tab, (st0, tuple(encf(1)) + tail, 0, far), d['n0'])
        if not _eqlift(got, (st0, tuple(encf(2)) + tail, 0, far)):
            raise NestError('validate p=1: %r' % (got,))
        for j in range(max(jlo, 1), jhi + 1):
            p = 2 ** (j + 1) - 1
            hop((st0, tuple(encf(p)) + tail, 0, far),
                (st, tuple(encin(2 ** (j - 1))) + tl(eA, j - 1, j), 0, fi),
                (cb, -1), j, 'boot j=%d' % j)
            laps(tl(eA, j - 1, j), 2 ** (j - 1), 2 ** j - 1,
                 'Atop j=%d' % j)
            hop((st, tuple(encin(2 ** j - 1)) + tl(eA, j - 1, j), 0, fi),
                (st, tuple(encin(2 ** (j - 1))) + tl(eB, j - 1, j), 0, fi),
                cAB, j - 1, 'ABtop j=%d' % j)
            nlap += 2 ** (j - 1) - 1
            for l in range(j - 1, 0, -1):
                laps(tl(eB, l, j), 2 ** l, 2 ** (l + 1) - 1,
                     'B%d j=%d' % (l, j))
                hop((st, tuple(encin(2 ** (l + 1) - 1)) + tl(eB, l, j), 0,
                     fi),
                    (st, tuple(encin(2 ** (l - 1))) + tl(eA, l - 1, j), 0,
                     fi),
                    cBA, l, 'BA%d j=%d' % (l, j))
                laps(tl(eA, l - 1, j), 2 ** (l - 1), 2 ** l - 1,
                     'A%d j=%d' % (l - 1, j))
                hop((st, tuple(encin(2 ** l - 1)) + tl(eA, l - 1, j), 0, fi),
                    (st, tuple(encin(2 ** (l - 1))) + tl(eB, l - 1, j), 0,
                     fi),
                    cAB, l - 1, 'AB%d j=%d' % (l - 1, j))
                nlap += 2 ** l - 1 + 2 ** (l - 1) - 1
            laps(tl(eB, 0, j), 1, 1, 'B0 j=%d' % j)
            bt = tuple(law['big_tail'])
            v0 = 2 ** (j + 1) + law.get('big_in', 0)
            hop((st, tuple(encin(1)) + tl(eB, 0, j), 0, fi),
                (st, tuple(encin(v0)) + bt, 0, fi),
                cCA, j, 'closeA j=%d' % j)
            laps(bt, v0, 2 ** (j + 2) - 1, 'BIG j=%d' % j)
            nlap += 2 ** (j + 2) - 1 - v0
            hop((st, tuple(encin(2 ** (j + 2) - 1)) + bt, 0, fi),
                (st0, tuple(encf(2 ** (j + 1))) + tail, 0, far),
                cCB, j, 'closeB j=%d' % j)
        d['nval'] = ('cascade (octave down): p=1 concrete + %d overflow '
                     'phases, j = %d..%d (%d levels, %d counts, '
                     '%d inner laps)'
                     % (jhi - max(jlo, 1) + 1, max(jlo, 1), jhi,
                        sum(j for j in range(max(jlo, 1), jhi + 1)),
                        sum(2 * j for j in range(max(jlo, 1), jhi + 1)),
                        nlap))
        return d['nval']
    for j in range(jlo, jhi + 1):
        p = 2 ** (j + 1) - 1
        hop((st0, tuple(encf(p)) + tail, 0, far),
            (st, tuple(encin(2 ** j)) + tl(eB, j, j), 0, fi),
            (cb, 0), j, 'boot j=%d' % j)
        for l in range(j, 0, -1):
            laps(tl(eB, l, j), 2 ** l, 2 ** (l + 1) - 1, 'B%d j=%d' % (l, j))
            hop((st, tuple(encin(2 ** (l + 1) - 1)) + tl(eB, l, j), 0, fi),
                (st, tuple(encin(2 ** (l - 1))) + tl(eA, l - 1, j), 0, fi),
                cBA, l, 'BA%d j=%d' % (l, j))
            laps(tl(eA, l - 1, j), 2 ** (l - 1), 2 ** l - 1,
                 'A%d j=%d' % (l - 1, j))
            hop((st, tuple(encin(2 ** l - 1)) + tl(eA, l - 1, j), 0, fi),
                (st, tuple(encin(2 ** (l - 1))) + tl(eB, l - 1, j), 0, fi),
                cAB, l - 1, 'AB%d j=%d' % (l - 1, j))
            nlap += 2 ** l - 1 + 2 ** (l - 1) - 1
        laps(tl(eB, 0, j), 1, 1, 'B0 j=%d' % j)
        hop((st, tuple(encin(1)) + tl(eB, 0, j), 0, fi),
            (st0, tuple(encf(2 ** (j + 1))) + tail, 0, far),
            cCL, j, 'close j=%d' % j)
    d['nval'] = ('cascade: %d overflow phases, j = %d..%d (%d levels, '
                 '%d counts, %d inner laps)'
                 % (jhi - jlo + 1, jlo, jhi,
                    sum(j + 1 for j in range(jlo, jhi + 1)),
                    sum(2 * j + 1 for j in range(jlo, jhi + 1)), nlap))
    return d['nval']


def _confs_ovf(ENCDATA, enc, st0, tail, far):
    """[emit_lapcert.confs]'s two overflow endpoints, rebuilt here so this
    section does not import its caller."""
    d = ENCDATA[enc]
    tail, far = tuple(tail), tuple(far)
    F = (far, (), 0, 0, ())
    if d['obS'] >= 1:
        B0 = (st0, (d['uS'], d['uS'], 1, d['obS'] - 1, d['soS'] + tail), 0, F)
    else:
        B0 = (st0, ((), d['uS'], 1, 0, d['soS'] + tail), 0, F)
    B1 = (st0, ((), d['uD'], 1, 1, d['soD'] + tail), 0, F)
    return B0, B1
