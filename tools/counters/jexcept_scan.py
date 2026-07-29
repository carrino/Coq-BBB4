#!/usr/bin/env python3
"""UNTRUSTED: the AFFINE-WITH-A-SMALL-j-EXCEPTION scan.

WAVE27 section 4b, John's first live read: `0RB0LB_1LC1RD_0RD0LC_1RB1LA` is
"a regular counter with a 0 to the left of every bit, and the carry has to
alternate states to cross these 0s."  Mechanically that machine's anchor
family is the ALREADY-WIRED `Alph_00_01_1`, the interior lap is exact affine
`4j+4`, and the overflow lap is `4j+6` **for j >= 2 with one concrete
exception at j = 1** (8 steps, not 10 -- the state-alternating carry at the
smallest width).

`emit_lapcert.validate` demands the affine law at EVERY anchor, so a single
exceptional j rejects the whole family: `derive` reports no chain, `degree()`
reads HIGHER, and the row is filed under `no inner family` or `no anchor`.
The boarding device for it already exists -- state the lap at `j = S j''`
and discharge the small j's as CONCRETE `vm_compute` laps (the offset
route's `j = 0` device, one octave up).

This scan MEASURES the shape across a machine list before anything is built:
for every candidate anchor family it reads the per-`j` lap cost off the raw
simulator and reports

    affine            both branches affine at every j (the flat route's own
                      shape -- if these appear, something else blocks them)
    jexc:i<a>/o<b>    affine for j >= a (interior) and j >= b (overflow),
                      with the smaller j's exceptional and CONSTANT in j
                      (i.e. finitely many concrete laps close the family)
    nonaffine         no affine law even above a small floor

Usage
  jexcept_scan.py --list FILE [--json OUT] [--pmax N]
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
from emit_interleave import parse, carry, LAB, DeriveError          # noqa: E402
from mirror_common import mirror_spec                               # noqa: E402
import lapcert as LC                                                # noqa: E402

# how far up the counter to measure; the exceptional j's live at the bottom
PMAX = 160
# per-lap step cap: laps here are affine, so a few hundred steps is plenty
LAPCAP = 4000
# the largest floor we are willing to call "a few concrete laps"
MAXFLOOR = 3


def lap_costs(spec, st0, encf, tail, far, pmax=PMAX):
    """cost[(j, ov)] = the step count of the lap E p -> E (succ p), measured
    on the RAW simulator, or None when the lap does not close at all.

    Returns (costs, bad) with costs a dict (j, ov) -> {p: steps} and bad the
    set of p whose lap never reached the successor within LAPCAP."""
    tab = parse(spec)
    tail, far = tuple(tail), LC.rstrip0(tuple(far))
    costs = collections.defaultdict(dict)
    bad = []
    # p = 1 is INCLUDED: [carry] makes it the j = 1 overflow anchor, and it is
    # exactly the anchor the flat route never measures (emit_lapcert.validate
    # starts at 2) and the one John's read says is exceptional.
    for p in range(1, pmax):
        j, ov = carry(p)
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st0, LC.rstrip0(tuple(encf(p + 1)) + tail), 0, far)
        cfg, hit = start, None
        for t in range(1, LAPCAP + 1):
            try:
                cfg = LC.wstep(tab, False, False, cfg)
            except LC.Halt:
                break
            if (cfg[0] == want[0] and cfg[2] == 0
                    and LC.rstrip0(cfg[1]) == want[1]
                    and LC.rstrip0(cfg[3]) == far):
                hit = t
                break
        if hit is None:
            bad.append(p)
        else:
            costs[(j, ov)][p] = hit
    return costs, bad


def _affine_floor(pts):
    """pts = {j: cost}, one cost per j (already checked constant in p).

    Returns (floor, (a, b)) with cost = a*j + b for every j >= floor, the
    SMALLEST such floor, or None.  floor 0 is the plain affine law."""
    js = sorted(pts)
    for f in range(0, MAXFLOOR + 1):
        hi = [j for j in js if j >= f]
        if len(hi) < 3:
            return None
        a = pts[hi[1]] - pts[hi[0]]
        if hi[1] - hi[0] != 1:
            continue
        b = pts[hi[0]] - a * hi[0]
        if all(pts[j] == a * j + b for j in hi):
            return f, (a, b)
    return None


def measure(spec, st0, encf, tail, far, pmax=PMAX):
    """Classify one candidate anchor family."""
    costs, bad = lap_costs(spec, st0, encf, tail, far, pmax)
    if bad:
        return dict(kind='open-lap', bad=bad[:8])
    if not costs:
        return dict(kind='no-lap')
    # every p at the same (j, ov) must cost the same, else the lap is not a
    # function of the carry index at all
    flat = {}
    for (j, ov), d in costs.items():
        vs = set(d.values())
        if len(vs) != 1:
            return dict(kind='p-dependent', at=(j, ov),
                        vals=sorted(vs)[:6])
        flat[(j, ov)] = vs.pop()
    ints = {j: c for (j, ov), c in flat.items() if not ov}
    ovfs = {j: c for (j, ov), c in flat.items() if ov}
    fi = _affine_floor(ints)
    fo = _affine_floor(ovfs)
    if fi is None or fo is None:
        return dict(kind='nonaffine',
                    ints=sorted(ints.items())[:8],
                    ovfs=sorted(ovfs.items())[:8])
    r = dict(ci=list(fi[1]), co=list(fo[1]), ifloor=fi[0], ofloor=fo[0],
             iexc={str(j): ints[j] for j in sorted(ints) if j < fi[0]},
             oexc={str(j): ovfs[j] for j in sorted(ovfs) if j < fo[0]},
             nint=len(ints), novf=len(ovfs))
    r['kind'] = ('affine' if fi[0] == 0 and fo[0] == 0 else
                 'jexc:i%d/o%d' % (fi[0], fo[0]))
    return r


def scan(spec, pmax=PMAX):
    """Best candidate over both growth directions and every anchor family."""
    RANK = {'affine': 0, 'jexc': 1}

    def rank(r):
        k = r['kind'].split(':')[0]
        return (RANK.get(k, 9),
                r.get('ifloor', 9) + r.get('ofloor', 9))
    best = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in EL.anchors(dspec):
            try:
                r = measure(dspec, LAB.index(edge), EL.ENC[enc], tail, far,
                            pmax)
            except (DeriveError, LC.Halt, KeyError):
                continue
            r.update(spec=spec, enc=enc, edge=edge, tail=list(tail),
                     far=list(far), mirror=mirrored)
            if best is None or rank(r) < rank(best):
                best = r
    return best or dict(spec=spec, kind='no-anchor-family')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('--pmax', type=int, default=PMAX)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    cnt = collections.Counter()
    res = []
    for i, spec in enumerate(specs):
        r = scan(spec, a.pmax)
        cnt[r['kind']] += 1
        res.append(r)
        extra = ''
        if 'ci' in r:
            extra = ('  [%s@%s tail=%s far=%s mir=%s  int %d*j+%d  ovf '
                     '%d*j+%d  iexc=%s oexc=%s]'
                     % (r['enc'], r['edge'], r['tail'], r['far'], r['mirror'],
                        r['ci'][0], r['ci'][1], r['co'][0], r['co'][1],
                        r['iexc'], r['oexc']))
        print('%4d/%d %-40s %-14s%s' % (i + 1, len(specs), spec, r['kind'],
                                        extra), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
