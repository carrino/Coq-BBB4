#!/usr/bin/env python3
"""UNTRUSTED: the ALTERNATING-OCTAVE (register x counter) anchor CHASE.

WAVE26 section 8b, John's read of `0RB0LC_1LC1RB_1LD1LA_1RD0RC`: "similar to
the counter, with ~3 extra columns to the left of the LSB, changing
110 -> 010 -> 000 on MSB carry."  Measured, the shape is sharper than a
growing register: the counter WORD is the ordinary `Alph_10_11_11` one, and
what varies is the anchor's FRAME -- the state and the constant cells on the
far side of the head:

    p = 4..7    StA, far = [S1]        (octave 2)
    p = 8..15   StA, far = []          (octave 3)
    p = 16..31  StA, far = [S1]        (octave 4)
    ...

`emit_lapcert.anchors` fixes ONE frame and validates it at every anchor, so a
two-frame family fails at the first octave boundary and the row is filed
`no anchor` / `no overflow phase`.  Nothing about the counter is unusual: the
family is a FINITE UNION of ordinary anchor forms indexed by the octave's
residue -- the same piecewise `Cc` the SKIP route already uses, one dimension
richer.

**The frame is CHASED, not guessed.**  An earlier version of this scan read
every frame each value was ever seen in and intersected them per octave; that
does not work, because the run passes a given value once per OUTER octave and
the intersection mixes those passes (measured on
`0RB0RD_1LA1RC_1RD1LC_0LC1RA`: the intersection offers `C@[] | C@[S1;S1]`,
and the `C@[S1;S1] -> C@[]` overflow then never closes, while the chase shows
the machine landing somewhere else entirely).  So this scan seeds on one rest
and walks the family FORWARD, reading each next anchor's frame off the
machine -- wave-27's own lesson ("read the LANDING off the machine instead of
assuming its padding"), one level up.

Reported per machine:

    plain           one frame at every anchor (what the flat route wants)
    period-<P>      the frame depends only on (octave mod P)
    grow-<u>        the far side grows by a fixed unit [u] per octave
    drift           the frame moves by no law this scan knows
    mid-octave      the frame changes INSIDE an octave

and, with --laps, what a board would have to prove:

    flat            every branch affine -- four ordinary chains and a
                    piecewise [Cc], no new theory
    nested-<n>      [n] of the overflow directions cost Theta(2^j): the
                    register step is an inner induction, not a chain

Usage
  regscan.py --list FILE [--laps] [--json OUT]
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_interleave import parse, carry, LAB                      # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
import lapcert as LC                                               # noqa: E402
import nestcert as NC                                              # noqa: E402

TAILMAX = 2
PMAX = 130                 # the top anchor the chase walks to
LAPCAP = 40000             # steps one lap may take before the chase gives up
FARMAX = 8                 # cells of far side a frame may carry
MINOCT = 5                 # octaves a periodic frame must survive
MAXP = 4


def octave(v):
    return v.bit_length() - 1


def seeds(spec, enc, tail, maxT=40000):
    """Candidate first anchors: blank-head rests whose left side is
    [E v ++ tail] for a small [v]."""
    tab = parse(spec)
    d = EL.ENCDATA[enc]
    A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
    tail = tuple(tail)
    out, seen = [], set()
    cfg = (0, (), 0, ())
    for t in range(maxT):
        q, l, h, r = cfg
        if (h == 0 and len(l) > len(tail)
                and tuple(l[len(l) - len(tail):]) == tail):
            if len(LC.rstrip0(r)) <= FARMAX:
                v = NC.decode(l[:len(l) - len(tail)], A, B, C)
                if v is not None and 2 <= v <= 24 and v not in seen:
                    seen.add(v)
                    out.append((v, cfg))
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def chase(spec, enc, tail, v0, cfg0, pmax=PMAX, cap=LAPCAP):
    """Walk the family FORWARD from one anchor, reading each next anchor's
    frame off the machine.

    Returns [(p, state, far, cost)] for p = v0 .. pmax: the first blank-head
    rest whose word reads [E p ++ tail], and how many steps the lap into it
    took.  Nothing about the frame is assumed."""
    tab = parse(spec)
    encf, tail = EL.ENC[enc], tuple(tail)
    out = [(v0, cfg0[0], LC.rstrip0(cfg0[3]), 0)]
    cfg = cfg0
    for p in range(v0, pmax):
        want = tuple(encf(p + 1)) + tail
        hit = None
        for t in range(1, cap + 1):
            try:
                cfg = LC.wstep(tab, False, False, cfg)
            except LC.Halt:
                return out
            if (cfg[2] == 0 and tuple(cfg[1]) == want
                    and len(LC.rstrip0(cfg[3])) <= FARMAX):
                hit = t
                break
        if hit is None:
            return out
        out.append((p + 1, cfg[0], LC.rstrip0(cfg[3]), hit))
    return out


def frame_law(walk):
    """How the frame moves along the chased family.

    The anchors AT a power of two are held out first: the chased exemplar
    rests at [E (2^k)] in a transient form ([StD], far empty) before settling
    into the octave's own frame, which is the SKIP route's virtual anchor one
    dimension up.  Folding those into a [VIRT] arm is what turns an apparent
    mid-octave change into a clean per-octave frame."""
    fr = {p: (q, f) for p, q, f, _ in walk}
    ps = sorted(fr)
    if len(ps) < 32:
        return dict(kind='short')
    byoct, virt = {}, {}
    for p in ps:
        k = octave(p)
        if (1 << k) < ps[0] or (1 << (k + 1)) - 1 > ps[-1]:
            continue        # only octaves fully inside the walk may speak
        if p == (1 << k):
            virt[k] = fr[p]
            continue        # held out; reconciled below
        if k in byoct and byoct[k] != fr[p]:
            return dict(kind='mid-octave', at=k)
        byoct.setdefault(k, fr[p])
    isvirt = any(virt.get(k) not in (None, byoct.get(k)) for k in byoct)
    ks = sorted(byoct)
    if len(ks) < 3:
        return dict(kind='short')
    vt = '+virt' if isvirt else ''
    if len(set(byoct.values())) == 1:
        return dict(kind='plain' + vt, period=1, k0=ks[0], octs=len(ks),
                    forms=[byoct[ks[0]]], virt=isvirt)
    for P in range(2, MAXP + 1):
        if len(ks) < max(MINOCT, P + 1):
            break
        if all(byoct[k] == byoct[ks[0] + ((k - ks[0]) % P)] for k in ks):
            return dict(kind='period-%d' % P + vt, period=P, k0=ks[0],
                        octs=len(ks), virt=isvirt,
                        forms=[byoct[ks[0] + i] for i in range(P)])
    (q0, f0), (q1, f1) = byoct[ks[0]], byoct[ks[1]]
    if q1 == q0 and len(f1) > len(f0) and f1[:len(f0)] == f0:
        u = f1[len(f0):]
        if all(byoct[k] == (q0, f0 + u * (k - ks[0])) for k in ks):
            return dict(kind='grow-%s' % ''.join(map(str, u)) + vt, period=1,
                        k0=ks[0], octs=len(ks), forms=[(q0, f0)],
                        grow=list(u), virt=isvirt)
    return dict(kind='drift', octs=len(ks), virt=isvirt,
                forms=[byoct[k] for k in ks[:6]])


def _affine(pts):
    """cost = a*j + b on every measured j (>= 3 of them), or None.

    The j's are NOT consecutive on an overflow branch: with period P the
    overflows of one residue class sit P apart (j = 2, 4, 6 at P = 2), so the
    slope is read off the gap and not off a unit step."""
    js = sorted(pts)
    if len(js) < 3:
        return None
    dj, num = js[1] - js[0], pts[js[1]] - pts[js[0]]
    if dj == 0 or num % dj:
        return None
    a = num // dj
    b = pts[js[0]] - a * js[0]
    return (a, b) if all(pts[j] == a * j + b for j in js) else None


def lap_law(walk, law, floor):
    """What a board would have to prove, from the chased costs: the interior
    and overflow laws of each residue class, and -- when the family has a
    virtual anchor at the powers of two -- the two laps that anchor carries.

    The lap INTO the virtual anchor is the ordinary overflow; the lap OUT of
    it is the REGISTER STEP, and that is the one to look at."""
    P, k0 = law.get('period', 1), law.get('k0', 0)
    ints = collections.defaultdict(dict)
    ovfs = collections.defaultdict(dict)
    vin, vout = {}, {}
    for p, _, _, cost in walk[1:]:
        src = p - 1                       # the cost is the lap FROM p-1
        if src < floor:
            continue
        k = octave(src)
        if law.get('virt') and src == (1 << k):
            vout[k] = cost
            continue
        if law.get('virt') and p == (1 << octave(p)):
            vin[octave(p)] = cost
            continue
        j, ov = carry(src)
        (ovfs if ov else ints)[(k - k0) % P][j] = cost
    if not ints:
        return dict(shape='short')
    if law.get('virt'):
        vl = _affine({k: c for k, c in vout.items()})
        ilaw = {i: _affine(d) for i, d in ints.items()}
        if any(v is None for v in ilaw.values()):
            return dict(shape='interior-nonaffine',
                        ints={i: sorted(d.items())[:6]
                              for i, d in ints.items()})
        return dict(shape='virt-flat' if vl else 'virt-EXP',
                    ci={i: list(v) for i, v in ilaw.items()},
                    vin=sorted(vin.items())[:5],
                    vout=sorted(vout.items())[:5],
                    vlaw=list(vl) if vl else None, floor=floor)
    if not ovfs:
        return dict(shape='short')
    ilaw = {i: _affine(d) for i, d in ints.items()}
    if any(v is None for v in ilaw.values()):
        return dict(shape='interior-nonaffine',
                    ints={i: sorted(d.items())[:6] for i, d in ints.items()})
    olaw = {i: _affine(d) for i, d in ovfs.items()}
    bad = sorted(i for i, v in olaw.items() if v is None)
    return dict(shape='flat' if not bad else 'nested-%d' % len(bad),
                ci={i: list(v) for i, v in ilaw.items()},
                co={i: (list(v) if v else None) for i, v in olaw.items()},
                expo=bad, floor=floor,
                oraw={i: sorted(d.items())[:5] for i, d in ovfs.items()
                      if i in bad})


def _tails():
    """Tail splits worth trying: the tail sits BETWEEN the counter word and
    the head, so it is part of the word's frame and not of the register."""
    out = [()]
    for n in range(1, TAILMAX + 1):
        out += [tuple((b >> i) & 1 for i in range(n)) for b in range(1 << n)]
    return out


def scan(spec, do_laps=False, pmax=PMAX):
    RANK = {'plain': 0, 'period': 1, 'grow': 4, 'drift': 6,
            'mid': 7, 'short': 8}
    SH = {'flat': 0, 'virt-flat': 1, 'nested-1': 2, 'virt-EXP': 3,
          'nested-2': 4, 'nested-3': 5}

    def rank(r):
        k = r['kind'].split('-')[0].replace('+virt', '')
        return (SH.get(r.get('shape'), 5) if do_laps else 0,
                RANK.get(k, 9), len(r.get('tail') or ()), -r.get('n', 0))
    best = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for enc in EL.ENCS:
            for tl in _tails():
                sd = seeds(dspec, enc, tl)
                if not sd:
                    continue
                v0, cfg0 = sd[0]
                walk = chase(dspec, enc, tl, v0, cfg0, pmax)
                r = frame_law(walk)
                r.update(spec=spec, enc=enc, tail=list(tl), mirror=mirrored,
                         n=len(walk), v0=v0)
                if do_laps and 'forms' in r and r['kind'] != 'drift':
                    r.update(lap_law(walk, r, max(8, v0)))
                if best is None or rank(r) < rank(best):
                    best = r
    return best or dict(spec=spec, kind='no-frame-family')


def _fmt(r):
    if 'forms' not in r:
        return '  [n=%d]' % r.get('n', 0)
    out = '  [%s@tail=%s mir=%s n=%d octs=%d  %s' % (
        r['enc'], r['tail'], r['mirror'], r['n'], r.get('octs', 0),
        ' | '.join('%s@%s' % (LAB[q], ''.join(map(str, f)) or '-')
                   for q, f in r['forms']))
    if r.get('grow'):
        out += ' +%s/oct' % ''.join(map(str, r['grow']))
    out += ']'
    if r.get('shape'):
        out += '  %s' % r['shape']
        if r.get('ci'):
            out += ' int=' + ','.join('%d*j+%d' % tuple(v)
                                      for v in r['ci'].values())
        if r.get('co'):
            out += ' ovf=' + ','.join('%d*j+%d' % tuple(v) if v else 'EXP'
                                      for v in r['co'].values())
        if r.get('vout'):
            out += ' virt-out=%s' % r['vout'][:4]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('--laps', action='store_true')
    ap.add_argument('--pmax', type=int, default=PMAX)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    cnt = collections.Counter()
    res = []
    for i, spec in enumerate(specs):
        r = scan(spec, a.laps, a.pmax)
        cnt[r.get('shape') or r['kind']] += 1
        res.append(r)
        print('%4d/%d %-40s %-12s%s' % (i + 1, len(specs), spec, r['kind'],
                                        _fmt(r)), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
