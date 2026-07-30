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
        gz = _int_chain(tab, Z0, Z1, 'j=0', b)
        gp = _int_chain(tab, P0, P1, 'j=S j', b)
        ints[b] = dict(Z0=Z0, Z1=gz[0], P0=P0, P1=gp[0],
                       chz=gz[1], chp=gp[1], cz=gz[2], cp=gp[2],
                       zpad=gz[3], ppad=gp[3])

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


def _int_chain(tab, A, T, what, b):
    """One half of the interior split: EXACT first, then up to `lift`.

    Wave-31: the exact-landing assertion, not the machines, is what filed rows
    at `no interior j=<half> chain`.  Measured over the open core rows, of the
    74 rows the two assertions filed, 30 derive at all four halves once `lift`
    is allowed and 44 stay blocked -- so the fallback is necessary and it is
    not sufficient, and the 44 are a fact about the machine.

    The slack is uniform where it occurs, and that is what makes it renderable:
    the LEFT side always lands exactly (it carries the opaque `E q0 ++ tail`,
    so a blank there would sit in the MIDDLE of the word and `lift` could not
    hide it) and the reached FAR side is the anchor's plus trailing blanks.
    Returns (landing, chain, (a, b), farpad) with `farpad` the blank count."""
    ch, r = _chain(tab, False, True, A, T)
    if ch is not None and r[0] == T and r[2] != 0:
        return T, ch, (r[1], r[2]), 0
    ch, r = _chain(tab, False, True, A, T, lift=True)
    if ch is None or r[2] == 0 or not LC._match(r[0], T, False, True, True):
        raise RegError('no interior %s chain at octave parity %d' % (what, b))
    got = r[0]
    if got[0] != T[0] or got[1] != T[1] or got[2] != T[2]:
        raise RegError('interior %s slack at octave parity %d is not on the '
                       'far side: %r vs %r' % (what, b, got, T))
    gp, wp = tuple(got[3][0]), tuple(T[3][0])
    if got[3][1:] != T[3][1:] or len(gp) <= len(wp) \
            or gp[:len(wp)] != wp or any(gp[len(wp):]):
        raise RegError('interior %s far slack at octave parity %d: %r vs %r'
                       % (what, b, got[3], T[3]))
    return got, ch, (r[1], r[2]), len(gp) - len(wp)


def _nested_ovf(tab, B0, B1, mid, K):
    """boot + inner counter + exit for an OVERFLOW arm at symbolic index K.

    The inner family is searched over `TRY`, not over `ENCS`.  Wave-32: this
    module registers three alphabets privately in `ENCDATA` -- `Alph_01_11_11`
    (the obS = 0 spelling of Mp's) and wave-30's two INVERTED rows -- and used
    them for the OUTER reader only, so the inner search could not see them.
    Measured over item (1)'s 39 rows, 60 nested arms: they open 26 arms across
    13 rows that reported `no inner family at pow2 j` with nothing at all, and
    24 of the 32 keys they contribute carry octave shift 1 (see `validate`).
    `ENCS` itself is untouched, so no other scan's search space moves.

    Wave-32 item (1): the inner run is searched by `nestcert.bounded_runs`, not
    `families`, so a family that starts at an OFFSET or stops at the HALF is
    found too.  The full-octave key still comes first AND still goes through
    `nestcert.endpoints` on the identical call, so a board that derived before
    derives the same way -- the new endpoints are reachable only by a key
    `families` returned nothing for."""
    cands = NC.bounded_runs(mid, ENCDATA, TRY, K=K)
    if not cands:
        raise RegError('no inner family at pow2 j')
    # The FURTHEST candidate's blocker, not the last one's.  With only
    # full-octave keys the distinction rarely bit; enumerating bounded runs as
    # well appends candidates that fail EARLY, and reporting the last of those
    # would move a row's label BACKWARDS purely because the search got wider.
    # Measured: 6 rows reported `no boot chain` before and `... not an sside`
    # after, and one went from `no inner interior chain` to `no boot chain`.
    fails = []
    for (key, lo, hi, shape) in cands[:24]:
        if shape == 'fill' and lo == 2 ** (K - 1 + key[4]):
            # the full-octave route, byte-for-byte the pre-wave-32 call
            CinS, CinF, AI0, AI1 = NC.endpoints(ENCDATA, None, None, (),
                                                (), key)
        else:
            ends = NC.bounded_endpoints(ENCDATA, key, lo, hi, shape)
            if ends is None:
                # the index-shift trap: the run's block count is j + oct - w
                # and an sside cannot carry a negative constant.  Buying the
                # headroom means peeling the OUTER index, which restates the
                # whole arm; filed, not chased.
                fails.append('inner run is not an sside at this octave')
                continue
            CinS, CinF, AI0, AI1 = ends
        chb, rb = _chain(tab, True, True, B0, CinS)
        if chb is None or rb[0] != CinS or rb[2] == 0:
            fails.append('no boot chain')
            continue
        chn, rn = _chain(tab, False, True, AI0, AI1)
        if chn is None or rn[0] != AI1 or rn[2] == 0:
            fails.append('no inner interior chain')
            continue
        che, re = _chain(tab, True, True, CinF, B1)
        if che is None or re[0] != B1:
            fails.append('no exit chain')
            continue
        return dict(key=key, CinS=CinS, CinF=CinF, AI0=AI0, AI1=AI1,
                    chb=chb, cb=(rb[1], rb[2]), chn=chn, cn=(rn[1], rn[2]),
                    che=che, ce=(re[1], re[2]),
                    # NOT `c`: a FLAT arm's `c` is its (a, b) cost tuple, and
                    # the two would share a key on the same `ovf` dict.
                    shape=shape, off=lo - 2 ** (hi.bit_length() - 1))
    raise RegError(max(fails, key=_rank) if fails else 'no inner family')


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
                # The inner family's OCTAVE SHIFT belongs in the replay bound.
                # `CinS` is `E_in (pow2 (j - 2 + oct) + c)` -- `nestcert`'s
                # endpoints put `oct` in the sside's constant `b` -- and an
                # `oct >= 1` family has `2^(j-2+oct)` laps, not `2^(j-2)`.
                # Wave-32: replaying from `1 << (j - 2)` walked the right
                # per-lap step counts (the low bits, hence the carry indices,
                # agree) but too FEW laps, landed short of the fill, and filed
                # the row `inner fill lands off the measured endpoint`.  That
                # is the whole of that 6-row bucket.
                #
                # Item (1): the run need not end at the fill.  `shape` says
                # where it does end, and the loop runs TO that value instead of
                # until the counter overflows -- which is the replay of exactly
                # the run `NestedLapLift.inner_to_add_lift` certifies.
                m = j - 2 + O['key'][4]
                v = (1 << m) + O.get('off', 0)
                vend = ((1 << (m + 1)) - 1 if O.get('shape', 'fill') == 'fill'
                        else (1 << m) + (1 << (m - 1)) - 1)
                while v < vend:
                    i, iov = carry(v)
                    if iov:
                        # k > tovf v0: the run would carry past its octave, so
                        # an intermediate anchor is NOT interior and [Hin] does
                        # not apply there.  The search rules this out; if it
                        # ever fires the search and the replay disagree.
                        raise RegError('p=%d inner run overflows at v=%d '
                                       '(end %d)' % (p, v, vend))
                    cur = EL.sim(tab, cur, O['cn'][0] * i + O['cn'][1])
                    ninner += 1
                    v += 1
                if not EL.eqlift(cur, _denc(O['CinF'], j - 2)):
                    raise RegError('p=%d inner %s -> %r want %r'
                                   % (p, O.get('shape', 'fill'), cur,
                                      _denc(O['CinF'], j - 2)))
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
    """A witness for every state at the overflow anchors of at least ONE
    octave parity.

    A state that fires in one arm and not the other is NOT a dead row: the
    overflow anchors alternate parity, so a single-parity witness reaches
    every anchor in at most one extra lap
    ([Counters/LapCertGluePar.vis_via_ovf_par_lift]).  Before wave-33 both
    parities were demanded here and the row was filed
    `no visit witness for state <q> at octave parity <b>'.

    On a nested arm the BOOT chain is tried first and the EXIT chain second.
    A state that fires only after the inner counter has run its `Theta(2^j)`
    laps has no prefix of the boot to witness it, and `vis_of_run` can see a
    prefix of ONE chain only; `NestedLapLift.vis_via_fill` bridges the two and
    is what `nestcert` has always used for this (its docstring measures the
    case at 8 of 30).  Wave-32: with the octave-shift replay fixed, this is
    where all 6 of the `inner fill lands off the endpoint` rows stop, so the
    fallback is what those rows were queued behind.

    Returns {state: {parity: ('boot'|'exit', chain)}}."""
    out = {}
    for q in range(4):
        pre = {}
        for b in (0, 1):
            O = D['ovf'][b]
            ch = O['ch'] if O['kind'] == 'flat' else O['chb']
            w = LC.reach_state(tab, True, True, O['B0'], ch, q)
            if w is not None:
                pre[b] = ('boot', w)
                continue
            if O['kind'] == 'nested':
                w = LC.reach_state(tab, True, True, O['CinF'], O['che'], q)
                if w is not None:
                    pre[b] = ('exit', w)
                    continue
        if not pre:
            raise RegError('no visit witness for state %s at either octave '
                           'parity' % LAB[q])
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

    @ISLACK@

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
                                  RegGlue@PARMOD@.
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

@VISBLOCK@
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
  - @ZPEEL@f_equal. rewrite H2. rshape_@ID@.
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
  - @PPEEL@f_equal. rewrite H2. rshape_@ID@.
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

OVF_NEST_GLUE_A = r'''Lemma gsn@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
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

Lemma gbo@B@_@ID@ : forall k, lift (cden [] [] k CS@B@_@ID@) = lift (Cin@B@ (pow2 @IPOWK@)).
Proof.
  intro k. f_equal.
  unfold Cin@B@_@ID@, cden, CS@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + @IOCT@) with @IPOWK@ by lia. replace (0 * k + 0) with 0 by lia.
  rewrite @IEPOW@. rshape_@ID@.
Qed.

'''

OVF_NEST_GLUE_FILL = r'''Lemma gxi@B@_@ID@ : forall k, Cin@B@ (fill (pow2 @IPOWK@)) = cden [] [] k CF@B@_@ID@.
Proof.
  intro k.
  destruct (@IENCM@.@INONE@ (fill (pow2 @IPOWK@)) @IPOWK@ (cview_fill_pow2 @IPOWK@)) as (H1 & _).
  unfold Cin@B@_@ID@, cden, CF@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + @IOCT@) with @IPOWK@ by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma hbo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin@B@ (pow2 @IPOWJ@)).
Proof.
  intros p j E Hb.
  exists (@CAB@ * j + @CBB@), (cden [] [] j CS@B@_@ID@).
  split; [lia|]. split; [| exact (gbo@B@_@ID@ j)].
  rewrite (gso@B@_@ID@ p j E Hb).
  exact (srun_sound tm true true chb@B@_@ID@ B0@B@_@ID@ CS@B@_@ID@ @CAB@ @CBB@
           run_boot@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cin@B@ (fill (pow2 @IPOWJ@))) = Some c'
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
  exact (nested_overflow_lift tm Cc Cin@B@ lapin@B@_@ID@ p (pow2 @IPOWJ@)
           (hbo@B@_@ID@ p j E Hb) (hxe@B@_@ID@ p j E Hb)).
Qed.

'''

# The HALFWAY tail: the inner run stops at [half2], not at the fill.  Only
# [gxi]/[hxe]/[lapo] differ -- [hbo] is verbatim the fill tail's, because the
# boot lands on the same octave start.  See `Counters/NestedLapHalf.v`.
OVF_NEST_GLUE_HALF = r'''Lemma ihalf@B@_@ID@ : forall n, @IENCF@ (half2 n) = rep @IUS@ n ++ @IUD@ ++ @ISOD@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gxi@B@_@ID@ : forall k, Cin@B@ (half2 @IHK@) = cden [] [] k CF@B@_@ID@.
Proof.
  intro k.
  unfold Cin@B@_@ID@, cden, CF@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + @IOCTM1@) with @IHK@ by lia. replace (0 * k + 0) with 0 by lia.
  rewrite ihalf@B@_@ID@. rshape_@ID@.
Qed.

Lemma hbo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin@B@ (pow2 @IPOWJ@)).
Proof.
  intros p j E Hb.
  exists (@CAB@ * j + @CBB@), (cden [] [] j CS@B@_@ID@).
  split; [lia|]. split; [| exact (gbo@B@_@ID@ j)].
  rewrite (gso@B@_@ID@ p j E Hb).
  exact (srun_sound tm true true chb@B@_@ID@ B0@B@_@ID@ CS@B@_@ID@ @CAB@ @CBB@
           run_boot@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cin@B@ (half2 @IHJ@)) = Some c'
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
    inside [NestedLapHalf.inner_to_half_lift]: the inner counter runs from
    [pow2 (S j)] to [half2 j] -- HALF its octave -- and stops there. *)
Lemma lapo@B@_@ID@ : forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_half_lift tm Cc Cin@B@ lapin@B@_@ID@ p @IHJ@
           (hbo@B@_@ID@ p j E Hb) (hxe@B@_@ID@ p j E Hb)).
Qed.

'''

VISX_HALF = r'''(** [VISX]'s twin for a HALFWAY arm: the exit fires from [half2], so the
    bridge is [NestedLapHalf.vis_via_half]. *)
Lemma visx@B@_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l CF@B@_@ID@ = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_csteps_of_lift tm Cc p q).
  apply (vis_via_half tm Cc Cin@B@ lapin@B@_@ID@ q p @IHJ@).
  - destruct (hbo@B@_@ID@ p j E Hb) as (n & c & _ & Hn & Hl).
    exists n, c. exact (conj Hn Hl).
  - apply (vis_lift_of_csteps tm
             (fun _ : positive => Cin@B@ (half2 @IHJ@)) xH).
    apply (vis_of_run tm (fun _ : positive => Cin@B@ (half2 @IHJ@))
                      true true l CF@B@_@ID@ xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi@B@_@ID@ j)].
Qed.

'''

VISX = r'''(** A state that fires in the parity-@BV@ arm's EXIT chain -- i.e. only after
    the inner counter has run its [Theta(2^j)] laps -- has no witness in the
    BOOT chain, and [vis_of_run] can see a prefix of one chain only.
    [NestedLapLift.vis_via_fill] bridges the two with the same [exists n] the
    lap uses, so nothing exponential is written down here either.

    Stated in the CONCRETE [csteps] form [viso@B@_@ID@] has, so the two are
    interchangeable at the use site: [vis_via_fill] lands in [lift] space and
    [LapCertGlueLift.vis_csteps_of_lift] pulls it straight back. *)
Lemma visx@B@_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l CF@B@_@ID@ = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = @BV@ ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_csteps_of_lift tm Cc p q).
  apply (vis_via_fill tm Cc Cin@B@ lapin@B@_@ID@ q p (pow2 @IPOWJ@)).
  - destruct (hbo@B@_@ID@ p j E Hb) as (n & c & _ & Hn & Hl).
    exists n, c. exact (conj Hn Hl).
  - apply (vis_lift_of_csteps tm
             (fun _ : positive => Cin@B@ (fill (pow2 @IPOWJ@))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin@B@ (fill (pow2 @IPOWJ@)))
                      true true l CF@B@_@ID@ xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi@B@_@ID@ j)].
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

VIS_HEAD = r"""(** ** Visits

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
"""

# The MIXED block, for a board where at least one state fires in ONE of the
# two overflow arms only.  The two arms are different runs, so a live state
# can have no prefix witness in one of them; [LapCertGluePar] weakens the
# premise for exactly those states -- the overflow anchors alternate parity,
# so a witness at one parity reaches every anchor in at most one extra lap.
# States witnessed at both parities keep the ordinary route verbatim.
VIS_MIXED_HEAD = r"""(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1].

    @PARWHO@ in ONE of the two arms only, which is not a reason to give
    up on it: the overflow anchors ALTERNATE parity, so a witness at a single
    parity is reached from every anchor in at most one extra lap.  That is
    [LapCertGluePar.vis_via_ovf_par_lift], whose premise ranges over the
    overflow anchors of one parity and which consumes the OVERFLOW lap
    [lapo_@ID@] to cross the octave boundary. *)

@VISO@@VISZ@Lemma vis_@ID@ : forall p q, (@P0@ <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q Hp.
  assert (H2 : (2 <= p)%positive).
  { apply Pos.le_trans with (@P0@)%positive; [| exact Hp].
    unfold Pos.le; vm_compute; discriminate. }
  destruct q.
@VISCASES@
Qed.
"""

VIS_BOTH_CASE = r"""  - (* @STQ@ fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_@ID@ @STQ@).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact visz@STQ@_@ID@.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (vis@W1@1_@ID@ @CH1@ @STQ@ ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (vis@W0@0_@ID@ @CH0@ @STQ@ ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1)."""

VIS_PAR_CASE = r"""  - (* @STQ@ fires in the parity-@PBV@ arm ONLY -- LapCertGluePar *)
    apply (vis_via_ovf_par_lift tm Cc lapi_@ID@ lapo_@ID@ @PBV@ @STQ@);
      [| exact H2].
    intros p1 j2 E1 Hb1. apply vis_lift_of_csteps.
    exact (vis@PW@@PB@_@ID@ @PCH@ @STQ@ ltac:(vm_compute; reflexivity)
             p1 j2 E1 Hb1)."""

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


def _far_peel(far, pad):
    """The blank-peeling tactic for ONE interior half's landing, or '' when
    that half landed exactly on the anchor's far side.

    `Nat.mul`/`Nat.add` have to be in the `cbn` list: the far count is
    `a * j + b` and `rewrite` does not compute, so without reducing it first
    the side reads `pre ++ rep [] (0 * j + 0) ++ [] ++ []` and
    `WTape.lift_app_blank` has no syntactic occurrence to match.  The EXACT
    template gets away without this because it finishes by `reflexivity`,
    which is up to conversion.

    The `change` nests one `++ [S0]` per surplus blank so each `rewrite`
    peels exactly one.  Never emitted with pad = 0: `lift_app_blank` would
    have nothing to rewrite and `rewrite !` would fail."""
    if not pad:
        return ''
    got = tuple(far) + (0,) * pad
    nest = ('(' * pad + clist(far)
            + ''.join(') ++ [S0]' for _ in range(pad)))
    return ('cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.\n    '
            'change (%s) with (%s).\n    ' % (clist(got), nest)
            + 'rewrite !lift_app_blank.\n    ')


def render(D):
    spec = D['spec']
    # The nested templates below state the inner run as
    # `inner_to_fill_lift ... (pow2 @IPOWJ@)` -- a run from the octave start TO
    # THE FILL.  A bounded arm (`nestcert.bounded_runs` shape 'half', or a
    # 'fill' run that starts at an offset) is a DIFFERENT run, and its board has
    # to cite `NestedLapLift.inner_to_add_lift` with the endpoint the search
    # measured.  Wave-32 derived no such row -- all 16 the reader opened stop at
    # an earlier gate (WAVE32_FINDINGS section 16) -- so that template is
    # deliberately NOT written on speculation.  Refuse loudly rather than emit
    # the fill template for a run that does not reach the fill: the board would
    # be wrong, and it would fail at `coqc` looking like an ordinary derivation
    # failure.
    for b, O in D['ovf'].items():
        if O['kind'] != 'nested':
            continue
        if O.get('shape', 'fill') == 'half' and not O.get('off', 0) \
                and O['key'][4] >= 1:
            continue            # wave-33: the HALFWAY template, below
        if O.get('shape', 'fill') != 'fill' or O.get('off', 0):
            raise RegError('bounded inner run at octave parity %d '
                           '(shape=%s, offset=%d) has no template yet'
                           % (b, O.get('shape', 'fill'), O.get('off', 0)))
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
                    '@CAP@': str(I['cp'][0]), '@CBP@': str(I['cp'][1]),
                    '@ZPEEL@': _far_peel(D['fr'][b], I['zpad']),
                    '@PPEEL@': _far_peel(D['fr'][b], I['ppad'])})
        idefs.append(_fill(INT_DEFS, r))
        iglue.append(_fill(INT_GLUE, r))
    iglue.append(INT_DISPATCH)

    # a state witnessed in the EXIT chain needs `visx@B@`, which only a nested
    # arm has; `visits` never files one against a flat arm.
    needx = set(b for q in range(4) for b in (0, 1)
                if b in D['vis'][q] and D['vis'][q][b][0] == 'exit')

    cindefs, odefs, oglue, iepows, viso = [], [], [], [], []
    halfmod = ''
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
            # The family's OCTAVE SHIFT.  It rides in the sside's constant
            # term (`nestcert.endpoints`: a = 1, b = oct), so the arm is stated
            # at `pow2 (j + oct)` throughout and the two `cden` bridges reindex
            # by it.  `oct = 0` renders exactly as before.
            o = O['key'][4]
            r.update({
                '@IOCT@': str(o),
                '@IPOWK@': 'k' if not o else '(k + %d)' % o,
                '@IPOWJ@': 'j' if not o else '(j + %d)' % o,
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
            half = O.get('shape', 'fill') == 'half'
            if half:
                # the octave start is [pow2 (S (j + o - 1))] and the endpoint
                # is [half2 (j + o - 1)]; [NestedLapHalf] states both at the
                # SAME index, so name it once and derive the start from it.
                hj = 'j' if o == 1 else '(j + %d)' % (o - 1)
                hk = 'k' if o == 1 else '(k + %d)' % (o - 1)
                r.update({'@IHJ@': hj, '@IHK@': hk,
                          '@IOCTM1@': str(o - 1),
                          '@IPOWJ@': '(S %s)' % hj,
                          '@IPOWK@': '(S %s)' % hk,
                          '@IUS@': clist(di['uS'])})
            cindefs.append(_fill(OVF_NEST_CIN, r))
            odefs.append(_fill(OVF_ENDS + OVF_NEST_DEFS, r))
            oglue.append(_fill(OVF_HEAD + OVF_NEST_GLUE_A
                               + (OVF_NEST_GLUE_HALF if half
                                  else OVF_NEST_GLUE_FILL), r))
            iepows.append(_fill(IEPOW, r))
            if half:
                halfmod = ' NestedLapHalf'
        viso.append(_fill(VISO, r))
        if b in needx:
            viso.append(_fill(
                VISX_HALF if (O['kind'] == 'nested'
                              and O.get('shape', 'fill') == 'half')
                else VISX, r))

    # the peel's leftover [p = 1], one concrete run per state
    zk = visz(parse(spec), D)
    vz = ''.join(_fill(VISZ, {'@STQ@': ST[q], '@KQ@': str(zk[q]),
                              '@ID@': ID}) for q in range(4))
    vzcases = '\n'.join('    + exact (visz%s_%s).' % (ST[q], ID)
                        for q in range(4))

    # A state witnessed at ONE parity only takes the [LapCertGluePar] route;
    # when every state is witnessed at both, the board renders exactly as it
    # did before wave-33 (this is the byte-identical case).
    single = {q: list(D['vis'][q])[0] for q in range(4)
              if len(D['vis'][q]) == 1}
    vis = ['', '']
    if not single:
        vis = []
        for b in (1, 0):
            blk = ['    + destruct q.']
            for q in range(4):
                where, ch = D['vis'][q][b]
                blk.append('      * exact (vis%s%d_%s %s %s '
                           'ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).'
                           % ('o' if where == 'boot' else 'x', b, ID,
                              EL.cchain(ch), ST[q]))
            vis.append('\n'.join(blk))

    if not single:
        visblock, parmod, viscases, parwho = VIS_HEAD, '', '', ''
    else:
        visblock, parmod = VIS_MIXED_HEAD, ' LapCertGluePar'
        cases = []
        for q in range(4):
            if q in single:
                b = single[q]
                where, ch = D['vis'][q][b]
                cases.append(_fill(VIS_PAR_CASE, {
                    '@STQ@': ST[q], '@ID@': ID, '@PB@': str(b),
                    '@PBV@': 'true' if b else 'false',
                    '@PW@': 'o' if where == 'boot' else 'x',
                    '@PCH@': EL.cchain(ch)}))
                continue
            r = {'@STQ@': ST[q], '@ID@': ID}
            for b in (0, 1):
                where, ch = D['vis'][q][b]
                r['@W%d@' % b] = 'o' if where == 'boot' else 'x'
                r['@CH%d@' % b] = EL.cchain(ch)
            cases.append(_fill(VIS_BOTH_CASE, r))
        viscases = '\n'.join(cases)
        qs = [ST[q] for q in sorted(single)]
        parwho = ('%s fires' % qs[0] if len(qs) == 1 else
                  '%s each fire' % ', '.join(qs))

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
        '@VISBLOCK@': visblock, '@PARMOD@': parmod + halfmod,
        '@VISCASES@': viscases, '@PARWHO@': parwho,
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
        '@ISLACK@': (
            'Every branch closes EXACTLY on the next anchor.'
            if not any(D['ints'][b][k] for b in (0, 1)
                       for k in ('zpad', 'ppad')) else
            'The interior halves marked below land one or more written blanks\n'
            '    past the anchor\'s FAR side and so close only up to [lift]\n'
            '    ([WTape.lift_app_blank]): %s.  The whole board is stated in\n'
            '    [lift] space anyway, so this costs nothing but the peel.'
            % ', '.join('parity %s %s +%d'
                        % ('true' if b else 'false', h, D['ints'][b][k])
                        for b in (1, 0)
                        for h, k in (('j=0', 'zpad'), ('j=S j', 'ppad'))
                        if D['ints'][b][k])),
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
         'no inner family at pow2 j',
         # a family WAS found and only its index shift is unstatable, so this
         # is further than "no family at all" and nearer than any chain gate
         'inner run is not an sside', 'no boot chain',
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
