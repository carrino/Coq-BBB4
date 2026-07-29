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


# --------------------------------------------------------------- process ---

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
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, nok = [], 0
    import collections as _c
    cnt = _c.Counter()
    for i, spec in enumerate(specs):
        r = scan(spec)
        res.append(r)
        nok += bool(r['ok'])
        cnt[r.get('why', 'OK')] += 1
        print('%4d/%d %-40s %s' % (i + 1, len(specs), spec,
                                   ('OK %s %s' % (r['enc'], r['val']))
                                   if r['ok'] else 'no: %s' % r['why'][:90]),
              flush=True)
    print('\n%d / %d fully derived' % (nok, len(specs)))
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
