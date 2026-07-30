#!/usr/bin/env python3
"""UNTRUSTED emitter: the TWO-FORM counter -- one plain counter whose anchor
FRAME (state, tail and far side) alternates by octave parity.

John's read of `0RB0RC_1LC1RB_0LD1RA_1RC1LD` (wave-29): "a pure counter with a
1 to the left of each bit, msb on the left", with "2 ones to the left of the
msb".  Confirmed mechanically at 15,630 consecutive steps out of 15,645 rests
-- and the alphabet that reads it (`bit b -> (b, 1)`, terminator `[S1;S1]`)
has been wired since wave-13.

What no reader offered was the FRAME: the family is

    Cc p = if podd p then (q1, E p ++ t1, S0, f1)
                     else (q0, E p ++ t0, S0, f0)

with `RegGlue.podd` the octave parity.  On the exemplar that is `C@[S1]` on
odd octaves and `C@[S0;S1;S1]` on even ones, and the UNION of the two keys
covers 8..255 with no gaps at all -- no skip, no virtual anchor, no register.
`anchors()` fixes ONE (state, tail, far) and validates it at every anchor, so
a two-form family fails at the first octave boundary and the row is filed
`no overflow phase at K=6`.  The whole bucket is this.

The lap branches, measured on the exemplar:

    interior   4j + 2   at BOTH parities, exact
    overflow   4j + 6   out of an even octave, exact
               Theta(2^j) out of an odd octave -- boot + inner counter + exit

so a NESTED branch again sits inside a piecewise `Cc`, this time on an
overflow arm.  `Counters/NestedLapLift.nested_overflow_lift` carries it,
`Counters/LapCertGlue` supplies reach/visits (there are no virtual anchors to
fence, so `SkipGlue` is not needed at all), and `LapGlue.glue_neverqh` closes.

Everything here is untrusted: the kernel re-runs `srun` on every chain, and
this module differentially validates EVERY branch against the raw simulator
-- exact step counts, exact configurations, lift-equal landings, and every
inner lap of every nested overflow -- before a board is written.

The renderer is `render` / `process` below: regcert's piecewise-`Cc` board with
the register dimension taken out and the two-form one put in.  It closes in
`lift` space throughout (`Counters/LapCertGlueLift.v`), which is what lets the
interior SPLIT be stated up to `lift`; the overflow arm is stated one peel
deeper than the flat route's and the `p = 1` case that reindex leaves behind is
refuted in `lap` and discharged concretely in `vis`.

Usage
  tailcert.py --list FILE [--emit] [--out JSON]
  tailcert.py --spec SPEC [--emit]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
import nestcert as NC                                              # noqa: E402
import lapcert as LC                                               # noqa: E402
from emit_lapcert import ENCDATA, ENC, ENCS, coqc                  # noqa: E402
from emit_interleave import (parse, LAB, ST, carry, mach_id,       # noqa: E402
                             coq_table, clist)
from mirror_common import mirror_spec, mirrorize                   # noqa: E402
from regcert import RegError, F, octave, _chain, _phase, _denc     # noqa: E402

PREFIX = 'REG'
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
VHI = 256
HI = 200

# The obS = 0 spelling of Mp's alphabet.  `theories/Counters/Alph_01_11_11.v`
# has been in the tree since the generated-alphabet wave; only this Python row
# was missing, and `Mp`'s own row carries obS = 1, whose overflow
# decomposition this route does not want.  Registered in ENCDATA but NOT in
# ENCS, so no other scan's search space (and no committed json) changes.
ENCDATA.setdefault('Alph_01_11_11',
                   dict(uS=(1, 1), sS=(0, 1), uD=(0, 1), sD=(1, 1),
                        obS=0, soS=(1, 1), soD=(1, 1),
                        fn='Ap_Alph_01_11_11', mod='Alph_01_11_11',
                        some='cview_some_Alph_01_11_11',
                        none='cview_none_Alph_01_11_11'))
ENC.setdefault('Alph_01_11_11', lambda m: _e01(m))


def _e01(m):
    out = []
    while m > 1:
        out += [m % 2, 1]
        m //= 2
    return out + [1, 1]


ENC['Alph_01_11_11'] = _e01


def _mk_enc(dig0, dig1, term):
    """`E xH = term`, `E (xO q) = dig0 ++ E q`, `E (xI q) = dig1 ++ E q` --
    the shape every alphabet in this development has (see gen_alphabet.py)."""
    def f(m):
        out = []
        while m > 1:
            out += list(dig1 if m % 2 else dig0)
            m //= 2
        return out + list(term)
    return f


# ---------------------------------------------------------------------------
# BIT-POLARITY INVERSION (wave-30).  John's read of
# `1RB1LC_0LC0RB_1LA1RD_1RC0RD` ("behaves very similar with msb on the left")
# and of `0RB1LA_0LC1RD_0LD1LD_1RB0LA` ("like a grey counter where it goes up
# then down") are the same fact: for 51 rows the reader matched the tape under
# an alphabet whose two DIGIT WORDS are the wrong way round, so the decoded
# value is the octave-wise complement of the machine's and the family reads
# DOWNWARD while the machine counts up.
#
# Measured on `0RB1LA_0LC1RD_0LD1LD_1RB0LA` under `Alph_10_11_11`: the plain
# decode has a longest consecutive +1 run of 0 (13 up / 12,915 down); the
# COMPLEMENT within each width has a run of 4,095 (12,915 up / 12 down).
#
# The alphabet that reads it directly swaps `dig(0)` and `dig(1)` and KEEPS the
# terminator.  `Jp` and `Alph_11_10_1` have the swapped digits but a one-cell
# terminator, so they match nothing; the partner of `Alph_10_11_11` is
# `Alph_11_10_11`, which did not exist.  Both new modules are generated by
# `gen_alphabet.py --abc <dig0>,<dig1>,<term>` and PROVED there, not asserted.
#
# Registered in ENCDATA but deliberately NOT in ENCS: `ENCS` is the search
# space of every other scan, and `reg113.json` / `quad35.json` / `jexc80.json`
# must keep reproducing.
# ---------------------------------------------------------------------------

INVERTED = {
    # tag                (dig0,        dig1,        terminator)
    'Alph_11_10_11':     ((1, 1),      (1, 0),      (1, 1)),
    'Alph_11_01_11':     ((1, 1),      (0, 1),      (1, 1)),
}

for _tag, (_d0, _d1, _t) in INVERTED.items():
    ENCDATA.setdefault(_tag, dict(
        uS=_d1, sS=_d0, uD=_d0, sD=_d1,
        obS=0, soS=_t, soD=_t,
        fn='Ap_' + _tag, mod=_tag,
        some='cview_some_' + _tag, none='cview_none_' + _tag))
    ENC.setdefault(_tag, _mk_enc(_d0, _d1, _t))

# alphabets this route offers, obS = 0 only (the overflow decomposition the
# board's glue states is `rep uS j ++ soS`).
TRY = (tuple(e for e in ENCS if ENCDATA[e]['obS'] == 0)
       + ('Alph_01_11_11',) + tuple(INVERTED))


# ------------------------------------------------------------------ read ---

def two_form(dspec, encs=None, maxtail=3, maxfar=3, maxT=400000,
             vlo=8, vhi=VHI):
    """A PAIR of anchor keys whose union is gap-free over [vlo, vhi) and which
    splits by octave parity.  Returns (enc, {parity: (state, tail, far)}, ks)
    or raises."""
    import collections as _c
    encs = encs or TRY
    tab = parse(dspec)
    luts = {e: {tuple(ENC[e](v)): v for v in range(1, vhi + 1)} for e in encs}
    # value SET per key, and the ARRIVAL ORDER of first sightings.  The order
    # is what says which WAY the family counts, and every route downstream
    # assumes `E p -> E (Pos.succ p)` -- see `_ascends` below.
    vals = _c.defaultdict(set)
    order = _c.defaultdict(list)
    cfg = (0, (), 0, ())
    for _ in range(maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        q, l, h, r = cfg
        if h:
            continue
        rr = LC.rstrip0(r)
        if len(rr) > maxfar:
            continue
        for k in range(maxtail + 1):
            if k > len(l) - 1:
                break
            w = tuple(l[:len(l) - k]) if k else tuple(l)
            tl = tuple(l[len(l) - k:]) if k else ()
            for e in encs:
                v = luts[e].get(w)
                if v is not None and vlo <= v < vhi:
                    key = (e, q, tl, rr)
                    if v not in vals[key]:
                        order[key].append(v)
                    vals[key].add(v)
    def _ascends(*ks):
        """Does the family count UP?  Wave-30: 51 rows were accepted here with
        a family the machine walks DOWNWARD -- gap-free as a SET, which is all
        this predicate used to check, and useless to every route downstream,
        which states `E p -> E (Pos.succ p)`.  No peel and no framing can
        recover an interior lap from a descending family; the fix is to read it
        under the alphabet whose digit words are the other way round (see
        INVERTED above), and to REFUSE the descending reading here so that the
        ascending one is the candidate that wins."""
        up = dn = run = 0
        for k in ks:
            seq = order[k]
            for i in range(len(seq) - 1):
                d = seq[i + 1] - seq[i]
                if d > 0:
                    up += 1
                elif d < 0:
                    dn += 1
                run += d == 1
        return run > 0 and up > dn

    keys = sorted(vals, key=lambda k: -len(vals[k]))[:40]
    best = None
    for i, a in enumerate(keys):
        for b in keys[i:]:
            if a[0] != b[0]:
                continue
            if not all(v in vals[a] or v in vals[b]
                       for v in range(vlo, vhi)):
                continue
            pa = {octave(v) for v in vals[a]}
            pb = {octave(v) for v in vals[b]}
            if a != b and (pa & pb):
                continue
            # the split must be by octave PARITY, not an arbitrary set
            oa = {k % 2 for k in pa}
            ob = {k % 2 for k in pb}
            if a != b and (len(oa) != 1 or len(ob) != 1 or oa == ob):
                continue
            if not _ascends(*({a, b})):
                continue
            ks = sorted(pa | pb)
            frames = {}
            frames[oa.pop() if a != b else 0] = a[1:]
            frames[ob.pop() if a != b else 1] = b[1:]
            score = (-len(ks), -len(vals[a]) - len(vals[b]))
            if best is None or score < best[0]:
                best = (score, a[0], frames, ks)
    if best is None:
        raise RegError('no gap-free two-form family')
    _, enc, frames, ks = best
    if len(ks) < 4:
        raise RegError('two-form family covers only %d octaves' % len(ks))
    return enc, frames, ks


# ------------------------------------------------------------ derivation ---

def derive(spec, mirrored=None, encs=None):
    last = None
    for mir in ((False, True) if mirrored is None else (mirrored,)):
        dspec = mirror_spec(spec) if mir else spec
        try:
            return _derive(spec, dspec, mir, encs)
        except RegError as e:
            last = str(e)
    raise RegError(last or 'no family')


def _derive(spec, dspec, mirrored, encs=None):
    tab = parse(dspec)
    enc, frames, ks = two_form(dspec, encs)
    d = ENCDATA[enc]
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    sS, sD = tuple(d['sS']), tuple(d['sD'])
    soS, soD = tuple(d['soS']), tuple(d['soD'])
    st = {b: frames[b][0] for b in (0, 1)}
    tl = {b: tuple(frames[b][1]) for b in (0, 1)}
    fr = {b: tuple(frames[b][2]) for b in (0, 1)}
    p0 = 1 << ks[0]

    # PEEL BEFORE ANYTHING ELSE.  The anchor's prefix is EMPTY on both sides,
    # so at j = 0 the head has no concrete cell to step onto and no window
    # step is available at all -- `derive_chain` returns nothing for every
    # framing.  The interior branch therefore SPLITS (j = 0 concrete, j = S j'
    # with one unit copy peeled into the prefix) and the overflow branch is
    # stated at j = S j' throughout, with `cview p = (1, None)` (that is,
    # p = 1) fenced off below p0.
    ints, ovf = {}, {}
    for b in (0, 1):
        Z0 = (st[b], (sS, (), 0, 0, ()), 0, F(fr[b]))
        Z1 = (st[b], (sD, (), 0, 0, ()), 0, F(fr[b]))
        P0 = (st[b], (uS, uS, 1, 0, sS), 0, F(fr[b]))
        P1 = (st[b], (uD, uD, 1, 0, sD), 0, F(fr[b]))
        chz, rz = _chain(tab, False, True, Z0, Z1)
        chp, rp = _chain(tab, False, True, P0, P1)
        if chz is None or rz[0] != Z1 or rz[2] == 0:
            raise RegError('no interior j=0 chain at octave parity %d' % b)
        if chp is None or rp[0] != P1 or rp[2] == 0:
            raise RegError('no interior j=S j chain at octave parity %d' % b)
        ints[b] = dict(Z0=Z0, Z1=Z1, P0=P0, P1=P1, chz=chz, chp=chp,
                       cz=(rz[1], rz[2]), cp=(rp[1], rp[2]))

    for b in (0, 1):
        nb = 1 - b
        B0 = (st[b], (uS, uS, 1, 0, soS + tl[b]), 0, F(fr[b]))
        B1 = (st[nb], ((), uD, 1, 2, soD + tl[nb]), 0, F(fr[nb]))
        ch, r = _chain(tab, True, True, B0, B1)
        if ch is not None and r[0] == B1 and r[2] > 0:
            ovf[b] = dict(kind='flat', B0=B0, B1=B1, ch=ch, c=(r[1], r[2]))
            continue
        # the exponential arm: boot + the inner counter's laps + exit
        K = max(k for k in ks[:-1] if k % 2 == b)
        p = (1 << (K + 1)) - 1        # cview p = (S K, None)
        src = (st[b], tuple(ENC[enc](p)) + tl[b], 0, fr[b])
        nxt = (st[nb], tuple(ENC[enc](p + 1)) + tl[nb], 0, fr[nb])
        mid = _phase(tab, src, (nxt[0], nxt[1], LC.rstrip0(nxt[3])))
        nest = _nested_ovf(tab, B0, B1, mid, K)
        ovf[b] = dict(kind='nested', B0=B0, B1=B1, **nest)

    D = dict(spec=dspec, orig=spec, mirror=mirrored, enc=enc,
             st=st, tl={b: list(tl[b]) for b in (0, 1)},
             fr={b: list(fr[b]) for b in (0, 1)},
             ks=ks, p0=p0, ints=ints, ovf=ovf)
    D['val'] = validate(tab, D)
    D['vis'] = visits(tab, D)
    D['boot'] = boot(tab, D)
    return D


def _nested_ovf(tab, B0, B1, mid, K):
    """boot + inner counter + exit for an OVERFLOW arm at symbolic index K."""
    keys = NC.families(mid, ENCDATA, ENCS, K=K)
    if not keys:
        raise RegError('no inner family at pow2 j')
    last = 'no inner family'
    for key in keys[:24]:
        CinS, CinF, AI0, AI1 = NC.endpoints(ENCDATA, None, None, (), (), key)
        chb, rb = _chain(tab, True, True, B0, CinS)
        if chb is None or rb[0] != CinS or rb[2] == 0:
            last = 'no boot chain'
            continue
        chn, rn = _chain(tab, False, True, AI0, AI1)
        if chn is None or rn[0] != AI1 or rn[2] == 0:
            last = 'no inner interior chain'
            continue
        che, re = _chain(tab, True, True, CinF, B1)
        if che is None or re[0] != B1:
            last = 'no exit chain'
            continue
        return dict(key=key, CinS=CinS, CinF=CinF, AI0=AI0, AI1=AI1,
                    chb=chb, cb=(rb[1], rb[2]), chn=chn, cn=(rn[1], rn[2]),
                    che=che, ce=(re[1], re[2]))
    raise RegError(last)


# ------------------------------------------------------------ validation ---

def _anchor(D, p):
    b = octave(p) % 2
    return (D['st'][b], tuple(ENC[D['enc']](p)) + tuple(D['tl'][b]), 0,
            tuple(D['fr'][b]))


def validate(tab, D, hi=HI):
    n, ninner, nnest = 0, 0, 0
    for p in range(D['p0'], hi):
        if octave(p + 1) > D['ks'][-1]:
            break
        start, want = _anchor(D, p), _anchor(D, p + 1)
        j, ov = carry(p)
        b = octave(p) % 2
        if ov:
            # the chain is stated at [cview p = (S j', None)] with one unit
            # copy peeled into the prefix, so its index is j - 2.
            if j < 2:
                continue
            O = D['ovf'][b]
            if O['kind'] == 'flat':
                steps = O['c'][0] * (j - 2) + O['c'][1]
            else:
                nnest += 1
                steps = O['cb'][0] * (j - 2) + O['cb'][1]
                cur = EL.sim(tab, start, steps)
                if not EL.eqlift(cur, _denc(O['CinS'], j - 2)):
                    raise RegError('p=%d boot -> %r want %r'
                                   % (p, cur, _denc(O['CinS'], j - 2)))
                v = 1 << (j - 2)
                while True:
                    i, iov = carry(v)
                    if iov:
                        break
                    cur = EL.sim(tab, cur, O['cn'][0] * i + O['cn'][1])
                    ninner += 1
                    v += 1
                if not EL.eqlift(cur, _denc(O['CinF'], j - 2)):
                    raise RegError('p=%d inner fill -> %r want %r'
                                   % (p, cur, _denc(O['CinF'], j - 2)))
                steps = O['ce'][0] * (j - 2) + O['ce'][1]
                start = cur
        else:
            I = D['ints'][b]
            steps = (I['cz'][1] if j == 0
                     else I['cp'][0] * (j - 1) + I['cp'][1])
        got = EL.sim(tab, start, steps)
        if not EL.eqlift(got, want):
            raise RegError('p=%d branch: %d steps -> %r want %r'
                           % (p, steps, got, want))
        n += 1
    return '%d anchors, %d nested overflows, %d inner laps' % (n, nnest,
                                                               ninner)


def visits(tab, D):
    """A witness for every state at EVERY overflow anchor, both parities.  On
    a nested arm the visible chain is the BOOT chain."""
    out = {}
    for q in range(4):
        pre = {}
        for b in (0, 1):
            O = D['ovf'][b]
            ch = O['ch'] if O['kind'] == 'flat' else O['chb']
            pre[b] = LC.reach_state(tab, True, True, O['B0'], ch, q)
            if pre[b] is None:
                raise RegError('no visit witness for state %s at octave '
                               'parity %d' % (LAB[q], b))
        out[q] = pre
    return out


def boot(tab, D):
    want = _anchor(D, D['p0'])
    cfg = (0, (), 0, ())
    for t in range(400000):
        if (cfg[0] == want[0] and cfg[2] == want[2]
                and LC.rstrip0(cfg[1]) == LC.rstrip0(want[1])
                and LC.rstrip0(cfg[3]) == LC.rstrip0(want[3])):
            return t
        cfg = LC.wstep(tab, False, False, cfg)
    raise RegError('no bootstrap to p0=%d' % D['p0'])


def visz(tab, D, nmax=400):
    """The PEELED overflow branch is stated at [cview p = (S (S j), None)], so
    the reindex leaves [cview p = (1, None)] -- that is, [p = 1] -- behind.
    [lap] never needs it ([p0 <= p] with [p0 >= 8] refutes it), but
    [LapCertGlueLift.vis_via_ovf_lift]'s premise ranges over EVERY overflow
    anchor, so every state needs a witness from the concrete [Cc 1]."""
    out, cfg = {}, _anchor(D, 1)
    for t in range(nmax):
        if cfg[0] not in out:
            out[cfg[0]] = t
        if len(out) == 4:
            return out
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    missing = [LAB[q] for q in range(4) if q not in out]
    raise RegError('no visit witness at the peeled p=1 for %s'
                   % ','.join(missing))


# ---------------------------------------------------------------- render ---
#
# The board is regcert's piecewise-[Cc] renderer with the register dimension
# taken out and the TWO-FORM one put in.  Three structural differences, all of
# them in [_derive] before they are here:
#
#  * there is no [virt]: the family is a plain counter and the frame is a
#    function of the octave PARITY alone, so [RegGlue.podd] is the whole
#    selector and [SkipGlue] is not needed at all;
#  * the interior branch is a SPLIT ([j = 0] concrete, [j = S j'] with one unit
#    copy peeled into the prefix) PER PARITY -- four chains where
#    [emit_lapcert.GLUE_SPLIT] has two;
#  * the overflow branch CROSSES parities (source frame [b], landing frame
#    [1 - b]) and is stated one peel deeper than the flat route's, at
#    [cview p = (S (S j), None)] with count [1*j+2] on the landing.  That
#    framing is why these rows derive here and not through
#    [emit_lapcert.derive].
#
# Everything closes in [lift] space ([LapCertGlueLift]): the interior split is
# where the [lift] fallback lives, and an exact landing is a [lift] one.

BOARD = r'''(** * REG_@ID@: machine @SPEC@, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the @ENCF@ digit alphabet (@ENCM@.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (@ST1@, (@ENCF@ p ++ @TL1@, S0, @FR1@))
                       else (@ST0@, (@ENCF@ p ++ @TL0@, S0, @FR0@))

    with [RegGlue.podd] the octave parity ([podd p = true] iff the octave is
    odd).  One counter, two frames, and their UNION covers every value with no
    gaps -- no skip, no virtual anchor, no register.  [LapDecider]'s
    [anchors()] fixes ONE frame and validates it at every anchor, so this
    family fails at the first octave boundary under every earlier reader and
    the rows were filed `no overflow phase at K=6'.

    The lap branches:

      interior  (cview p = (j, Some q0)), SPLIT and per parity:
                j = 0 concrete, j = S j' with one unit copy peeled into the
                chain's prefix -- @CIZ@ / @CIP@ by parity
      overflow  (cview p = (S (S j), None)), one arm per parity, CROSSING into
                the other parity's frame: @CO@

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [@P0@ <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations@VNEST@ -- for @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  @MODS@ LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf :=
  if podd p then (@ST1@, (@ENCF@ p ++ @TL1@, S0, @FR1@))
  else (@ST0@, (@ENCF@ p ++ @TL0@, S0, @FR0@)).
Local Notation Cc := Cc_@ID@.

@CINDEFS@Ltac rshape_@ID@ :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

@INTDEFS@@OVFDEFS@(** ** Anchor glue -- the only per-machine mathematics *)

@IEPOWS@@INTGLUE@@OVFGLUE@(** ** The lap *)

Lemma lapo_@ID@ : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_@ID@ p j E Hb).
  - exact (lapo0_@ID@ p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [@P0@]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_@ID@ : forall p, (@P0@ <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_@ID@ p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_@ID@ p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with
              | Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1]. *)

@VISO@@VISZ@Lemma vis_@ID@ : forall p q, (@P0@ <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q _.
  apply (vis_via_ovf_lift tm Cc lapi_@ID@ q).
  intros p1 j1 E1. destruct j1 as [|j2].
  - assert (H1 : p1 = 1%positive)
      by (rewrite (cview_none_shape p1 0 E1); reflexivity).
    subst p1. apply vis_lift_of_csteps. destruct q.
@VISZCASES@
  - apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
@VISITS1@
@VISITS0@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc @P0@). - exact boot_@ID@. - intros p Hp. apply (lap_@ID@ p Hp). - intros p q Hp. apply (vis_@ID@ p q Hp). Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

INT_DEFS = r'''(** *** the interior branch at octave parity @BV@, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z0@B@_@ID@ : sconf := @Z0@.
Definition Z1@B@_@ID@ : sconf := @Z1@.
Definition chz@B@_@ID@ : list lstep := @CHZ@.

Lemma run_z@B@_@ID@ : srun tm false true chz@B@_@ID@ Z0@B@_@ID@ = Some (Z1@B@_@ID@, @CAZ@, @CBZ@).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P0@B@_@ID@ : sconf := @P0C@.
Definition P1@B@_@ID@ : sconf := @P1C@.
Definition chp@B@_@ID@ : list lstep := @CHP@.

Lemma run_p@B@_@ID@ : srun tm false true chp@B@_@ID@ P0@B@_@ID@ = Some (P1@B@_@ID@, @CAP@, @CBP@).
Proof. vm_compute. reflexivity. Qed.

'''

INT_GLUE = r'''Lemma gz@B@_@ID@ : forall p q0, cview p = (0, Some q0) -> podd p = @BV@ ->
  Cc p = cden (@ENCF@ q0 ++ @TL@) [] 0 Z0@B@_@ID@ /\
  lift (cden (@ENCF@ q0 ++ @TL@) [] 0 Z1@B@_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (@ENCM@.@SOME@ p 0 q0 E) as (H1 & H2).
  unfold Cc_@ID@. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z0@B@_@ID@, Z1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_@ID@.
  - f_equal. rewrite H2. rshape_@ID@.
Qed.

Lemma gp@B@_@ID@ : forall p j q0, cview p = (S j, Some q0) -> podd p = @BV@ ->
  Cc p = cden (@ENCF@ q0 ++ @TL@) [] j P0@B@_@ID@ /\
  lift (cden (@ENCF@ q0 ++ @TL@) [] j P1@B@_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (@ENCM@.@SOME@ p (S j) q0 E) as (H1 & H2).
  unfold Cc_@ID@. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P0@B@_@ID@, P1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_@ID@.
  - f_equal. rewrite H2. rshape_@ID@.
Qed.

Lemma lapi@B@_@ID@ : forall p j q0, cview p = (j, Some q0) -> podd p = @BV@ ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz@B@_@ID@ p q0 E Hb) as (HA & HB).
    exists (@CAZ@ * 0 + @CBZ@), (cden (@ENCF@ q0 ++ @TL@) [] 0 Z1@B@_@ID@).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz@B@_@ID@ Z0@B@_@ID@ Z1@B@_@ID@ @CAZ@ @CBZ@
             run_z@B@_@ID@ (@ENCF@ q0 ++ @TL@) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp@B@_@ID@ p j' q0 E Hb) as (HA & HB).
    exists (@CAP@ * j' + @CBP@), (cden (@ENCF@ q0 ++ @TL@) [] j' P1@B@_@ID@).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp@B@_@ID@ P0@B@_@ID@ P1@B@_@ID@ @CAP@ @CBP@
             run_p@B@_@ID@ (@ENCF@ q0 ++ @TL@) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

'''

INT_DISPATCH = r'''Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_@ID@ p j q0 E Hb).
  - exact (lapi0_@ID@ p j q0 E Hb).
Qed.

'''

# The overflow arm's endpoints, shared by the flat and the nested kind: the
# source at parity @BV@ and the landing in the OTHER parity's frame.
OVF_ENDS = r'''Definition B0@B@_@ID@ : sconf := @B0@.
Definition B1@B@_@ID@ : sconf := @B1@.

'''

OVF_HEAD = r'''(** *** the overflow branch out of an octave of parity @BV@.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  Cc p = cden [] [] j B0@B@_@ID@.
Proof.
  intros p j E Hb. destruct (@ENCM@.@NONE@ p (S j) E) as (H1 & _).
  unfold Cc_@ID@. rewrite Hb.
  unfold cden, B0@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma geo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  cden [] [] j B1@B@_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (@ENCM@.@NONE@ p (S j) E) as (_ & H2).
  unfold Cc_@ID@. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

'''

OVF_FLAT_DEFS = r'''(** *** the overflow arm at octave parity @BV@: FLAT, @CAO@*j+@CBO@ steps *)
Definition cho@B@_@ID@ : list lstep := @CHO@.

Lemma run_ovf@B@_@ID@ : srun tm true true cho@B@_@ID@ B0@B@_@ID@ = Some (B1@B@_@ID@, @CAO@, @CBO@).
Proof. vm_compute. reflexivity. Qed.

'''

OVF_FLAT_GLUE = r'''Lemma lapo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (@CAO@ * j + @CBO@), (cden [] [] j B1@B@_@ID@).
  split; [| split; [f_equal; exact (geo@B@_@ID@ p j E Hb) | lia]].
  rewrite (gso@B@_@ID@ p j E Hb).
  exact (srun_sound tm true true cho@B@_@ID@ B0@B@_@ID@ B1@B@_@ID@ @CAO@ @CBO@
           run_ovf@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

'''

OVF_NEST_CIN = r'''(** ** The INNER anchor family of the parity-@BV@ overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin@B@_@ID@ (v : positive) : cconf :=
  (@ISTN@, (@IENCF@ v ++ @ITAIL@, S0, @IFAR@)).
Local Notation Cin@B@ := Cin@B@_@ID@.

'''

OVF_NEST_DEFS = r'''(** *** the overflow arm at octave parity @BV@: boot @CAB@*j+@CBB@, then the
    inner counter's laps, then exit @CAE@*j+@CBE@ *)
Definition CS@B@_@ID@ : sconf := @CS@.
Definition chb@B@_@ID@ : list lstep := @CHB@.

Lemma run_boot@B@_@ID@ : srun tm true true chb@B@_@ID@ B0@B@_@ID@ = Some (CS@B@_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.

Definition AI0@B@_@ID@ : sconf := @AI0@.
Definition AI1@B@_@ID@ : sconf := @AI1@.
Definition chn@B@_@ID@ : list lstep := @CHN@.

Lemma run_inner@B@_@ID@ : srun tm false true chn@B@_@ID@ AI0@B@_@ID@ = Some (AI1@B@_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed.

Definition CF@B@_@ID@ : sconf := @CF@.
Definition che@B@_@ID@ : list lstep := @CHE@.

Lemma run_exit@B@_@ID@ : srun tm true true che@B@_@ID@ CF@B@_@ID@ = Some (B1@B@_@ID@, @CAE@, @CBE@).
Proof. vm_compute. reflexivity. Qed.

'''

IEPOW = ('Lemma iepow@B@_@ID@ : forall n, @IENCF@ (pow2 n) = rep @IUD@ n ++ @ISOD@.\n'
         'Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.\n\n')

OVF_NEST_GLUE = r'''Lemma gsn@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  Cin@B@ v = cden (@IENCF@ q0 ++ @ITAIL@) [] i AI0@B@_@ID@.
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (H1 & _).
  unfold Cin@B@_@ID@, cden, AI0@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gen@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  cden (@IENCF@ q0 ++ @ITAIL@) [] i AI1@B@_@ID@ = Cin@B@ (Pos.succ v).
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (_ & H2).
  unfold Cin@B@_@ID@, cden, AI1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapin@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin@B@ v) = Some c'
               /\ lift c' = lift (Cin@B@ (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (@CAN@ * i + @CBN@), (Cin@B@ (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn@B@_@ID@ v i q0 E).
  rewrite (srun_sound tm false true chn@B@_@ID@ AI0@B@_@ID@ AI1@B@_@ID@ @CAN@ @CBN@
             run_inner@B@_@ID@ (@IENCF@ q0 ++ @ITAIL@) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen@B@_@ID@ v i q0 E).
Qed.

Lemma gbo@B@_@ID@ : forall k, lift (cden [] [] k CS@B@_@ID@) = lift (Cin@B@ (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin@B@_@ID@, cden, CS@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite @IEPOW@. rshape_@ID@.
Qed.

Lemma gxi@B@_@ID@ : forall k, Cin@B@ (fill (pow2 k)) = cden [] [] k CF@B@_@ID@.
Proof.
  intro k.
  destruct (@IENCM@.@INONE@ (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin@B@_@ID@, cden, CF@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma hbo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin@B@ (pow2 j)).
Proof.
  intros p j E Hb.
  exists (@CAB@ * j + @CBB@), (cden [] [] j CS@B@_@ID@).
  split; [lia|]. split; [| exact (gbo@B@_@ID@ j)].
  rewrite (gso@B@_@ID@ p j E Hb).
  exact (srun_sound tm true true chb@B@_@ID@ B0@B@_@ID@ CS@B@_@ID@ @CAB@ @CBB@
           run_boot@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cin@B@ (fill (pow2 j))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (@CAE@ * j + @CBE@), (cden [] [] j B1@B@_@ID@).
  split; [| f_equal; exact (geo@B@_@ID@ p j E Hb)].
  rewrite (gxi@B@_@ID@ j).
  exact (srun_sound tm true true che@B@_@ID@ CF@B@_@ID@ B1@B@_@ID@ @CAE@ @CBE@
           run_exit@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The [Theta(2^j)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_lift tm Cc Cin@B@ lapin@B@_@ID@ p (pow2 j)
           (hbo@B@_@ID@ p j E Hb) (hxe@B@_@ID@ p j E Hb)).
Qed.

'''

VISO = r'''Lemma viso@B@_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B0@B@_@ID@ = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B0@B@_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso@B@_@ID@ p j E Hb)].
Qed.

'''

VISZ = ('(** State @STQ@ at the peel\'s leftover overflow anchor [p = 1]. *)\n'
        'Lemma visz@STQ@_@ID@ : exists k c, csteps tm k (Cc 1) = Some c '
        '/\\ fst c = @STQ@.\n'
        'Proof. exists @KQ@. eexists. split; '
        '[vm_compute; reflexivity | reflexivity]. Qed.\n\n')


def _fill(tpl, reps):
    out = tpl
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


def _sub(D, b):
    """The per-parity substitutions every arm shares."""
    return {'@B@': str(b), '@BV@': 'true' if b else 'false',
            '@TL@': clist(D['tl'][b]), '@FR@': clist(D['fr'][b])}


def render(D):
    spec = D['spec']
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    encf = d.get('fn') or D['enc']
    mods = []
    for m in ([d['mod']] + [ENCDATA[O['key'][0]]['mod']
                            for O in D['ovf'].values()
                            if O['kind'] == 'nested']):
        if m not in mods and m not in ('JpCounter', 'MonoCounter', 'WTape'):
            mods.append(m)

    idefs, iglue = [], []
    for b in (1, 0):
        I = D['ints'][b]
        r = dict(_sub(D, b),
                 **{'@Z0@': EL.cconf(I['Z0']), '@Z1@': EL.cconf(I['Z1']),
                    '@P0C@': EL.cconf(I['P0']), '@P1C@': EL.cconf(I['P1']),
                    '@CHZ@': EL.cchain(I['chz']), '@CHP@': EL.cchain(I['chp']),
                    '@CAZ@': str(I['cz'][0]), '@CBZ@': str(I['cz'][1]),
                    '@CAP@': str(I['cp'][0]), '@CBP@': str(I['cp'][1])})
        idefs.append(_fill(INT_DEFS, r))
        iglue.append(_fill(INT_GLUE, r))
    iglue.append(INT_DISPATCH)

    cindefs, odefs, oglue, iepows, viso = [], [], [], [], []
    for b in (1, 0):
        O = D['ovf'][b]
        r = dict(_sub(D, b),
                 **{'@B0@': EL.cconf(O['B0']), '@B1@': EL.cconf(O['B1'])})
        if O['kind'] == 'flat':
            r.update({'@CHO@': EL.cchain(O['ch']),
                      '@CAO@': str(O['c'][0]), '@CBO@': str(O['c'][1])})
            odefs.append(_fill(OVF_ENDS + OVF_FLAT_DEFS, r))
            oglue.append(_fill(OVF_HEAD + OVF_FLAT_GLUE, r))
        else:
            di = ENCDATA[O['key'][0]]
            r.update({
                '@CS@': EL.cconf(O['CinS']), '@CF@': EL.cconf(O['CinF']),
                '@AI0@': EL.cconf(O['AI0']), '@AI1@': EL.cconf(O['AI1']),
                '@CHB@': EL.cchain(O['chb']), '@CHN@': EL.cchain(O['chn']),
                '@CHE@': EL.cchain(O['che']),
                '@CAB@': str(O['cb'][0]), '@CBB@': str(O['cb'][1]),
                '@CAN@': str(O['cn'][0]), '@CBN@': str(O['cn'][1]),
                '@CAE@': str(O['ce'][0]), '@CBE@': str(O['ce'][1]),
                '@IENCF@': di.get('fn') or O['key'][0], '@IENCM@': di['mod'],
                '@ISOME@': di['some'], '@INONE@': di['none'],
                '@ITAIL@': clist(O['key'][2]), '@IFAR@': clist(O['key'][3]),
                '@ISTN@': ST[O['key'][1]],
                '@IEPOW@': 'iepow%d_%s' % (b, ID),
                '@IUD@': clist(di['uD']), '@ISOD@': clist(di['soD'])})
            cindefs.append(_fill(OVF_NEST_CIN, r))
            odefs.append(_fill(OVF_ENDS + OVF_NEST_DEFS, r))
            oglue.append(_fill(OVF_HEAD + OVF_NEST_GLUE, r))
            iepows.append(_fill(IEPOW, r))
        viso.append(_fill(VISO, r))

    # the peel's leftover [p = 1], one concrete run per state
    zk = visz(parse(spec), D)
    vz = ''.join(_fill(VISZ, {'@STQ@': ST[q], '@KQ@': str(zk[q]),
                              '@ID@': ID}) for q in range(4))
    vzcases = '\n'.join('    + exact (visz%s_%s).' % (ST[q], ID)
                        for q in range(4))

    vis = []
    for b in (1, 0):
        blk = ['    + destruct q.']
        for q in range(4):
            blk.append('      * exact (viso%d_%s %s %s '
                        'ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).'
                        % (b, ID, EL.cchain(D['vis'][q][b]), ST[q]))
        vis.append('\n'.join(blk))

    nest = [b for b in (1, 0) if D['ovf'][b]['kind'] == 'nested']
    reps = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@MODS@': ' '.join(mods),
        '@ENCF@': encf, '@ENCM@': d['mod'],
        '@SOME@': d['some'], '@NONE@': d['none'],
        '@ST1@': ST[D['st'][1]], '@ST0@': ST[D['st'][0]],
        '@TL1@': clist(D['tl'][1]), '@TL0@': clist(D['tl'][0]),
        '@FR1@': clist(D['fr'][1]), '@FR0@': clist(D['fr'][0]),
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@CINDEFS@': ''.join(cindefs),
        '@INTDEFS@': ''.join(idefs), '@INTGLUE@': ''.join(iglue),
        '@OVFDEFS@': ''.join(odefs), '@OVFGLUE@': ''.join(oglue),
        '@IEPOWS@': ''.join(iepows),
        '@VISO@': ''.join(viso), '@VISZ@': vz, '@VISZCASES@': vzcases,
        '@VISITS1@': vis[0], '@VISITS0@': vis[1],
        '@CIZ@': '%d*j+%d / %d*j+%d' % (D['ints'][1]['cz']
                                        + D['ints'][0]['cz']),
        '@CIP@': '%d*j+%d / %d*j+%d' % (D['ints'][1]['cp']
                                        + D['ints'][0]['cp']),
        '@CO@': '; '.join(
            'parity %s %s' % ('true' if b else 'false',
                              ('FLAT %d*j+%d' % D['ovf'][b]['c'])
                              if D['ovf'][b]['kind'] == 'flat' else
                              ('NESTED, boot %d*j+%d then the inner counter '
                               'then exit %d*j+%d'
                               % (D['ovf'][b]['cb'] + D['ovf'][b]['ce'])))
            for b in (1, 0)),
        '@VNEST@': (', and every inner lap of every nested overflow'
                    if nest else ''),
        '@VAL@': D['val'],
    }
    out = BOARD
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


# --------------------------------------------------------------- process ---


def process(spec, do_emit=False, force=False, encs=None):
    D = derive(spec, encs=encs)
    if not do_emit:
        return dict(spec=spec, ok=True, enc=D['enc'], p0=D['p0'], val=D['val'])
    path = os.path.join(OUTDIR, '%s_%s.v' % (PREFIX, mach_id(spec)))
    if os.path.exists(path) and not force:
        return dict(spec=spec, ok=True, enc=D['enc'], file=path, skipped=True,
                    val=D['val'])
    src = render(D)
    if D['mirror']:
        src = mirrorize(src, spec, D['spec'])
    open(path, 'w').write(src)
    ok, log = coqc(os.path.relpath(path, REPO))
    if not ok:
        os.remove(path)
        lg = [l for l in log.strip().splitlines() if l.strip()]
        raise RegError('coqc: ' + '\n'.join(lg[-8:]))
    return dict(spec=spec, ok=True, enc=D['enc'], file=path, val=D['val'])

# How far a row got, so a machine whose direct orientation reaches the inner
# family is not filed under whatever its MIRROR did (nestcert's lesson).
_RANK = ['no gap-free two-form family', 'two-form family covers only',
         'no interior j=0 chain', 'no interior j=S j chain',
         'no inner family at pow2 j', 'no boot chain',
         'no inner interior chain', 'no exit chain',
         'no visit witness', 'no bootstrap']


def _rank(msg):
    for i, k in enumerate(_RANK):
        if msg.startswith(k):
            return i
    return len(_RANK)


def scan(spec):
    """Read the two-form family and derive as much of the certificate as this
    module can, reporting the FURTHEST gate either orientation reached."""
    best, why = -1, 'no family'
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        try:
            D = _derive(spec, dspec, mir)
            return dict(spec=spec, ok=True, enc=D['enc'], mirror=mir,
                        p0=D['p0'], val=D['val'])
        except RegError as e:
            msg = str(e)
        except Exception as e:                                 # noqa: BLE001
            msg = '%s: %s' % (type(e).__name__, e)
        if _rank(msg) > best:
            best, why = _rank(msg), msg
    return dict(spec=spec, ok=False, why=why)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    ap.add_argument('--emit', action='store_true',
                    help='render the board and compile it')
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, nok = [], 0
    import collections as _c
    cnt = _c.Counter()
    for i, spec in enumerate(specs):
        if a.emit:
            try:
                r = process(spec, True, a.force)
            except Exception as e:                              # noqa: BLE001
                r = dict(spec=spec, ok=False,
                         why='%s: %s' % (type(e).__name__, e))
        else:
            r = scan(spec)
        res.append(r)
        nok += bool(r['ok'])
        cnt[r.get('why', 'OK')] += 1
        print('%4d/%d %-40s %s' % (i + 1, len(specs), spec,
                                   ('OK %s %s' % (r['enc'], r['val']))
                                   if r['ok'] else 'no: %s' % r['why'][:400]),
              flush=True)
    print('\n%d / %d %s' % (nok, len(specs),
                            'boarded' if a.emit else 'fully derived'))
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
