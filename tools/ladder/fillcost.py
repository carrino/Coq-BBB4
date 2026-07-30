#!/usr/bin/env python3
"""UNTRUSTED measurement: how EXPENSIVE is one fill, as a function of width?

The fill arm is a rung-two object only if the machine crosses `E(p, b^p-1) ->
E(p', c)` in a number of steps that is AFFINE in the family's own run counts.
Every arm's step count is a sum of the `fired` expressions the replay engine
accumulates, and those are affine in the free variables of the arm's lhs -- so
a fill whose raw cost grows like `2^p` cannot be one arm however the search is
widened.  That is a property of the machine, measurable without any arm being
built, so it is measured here rather than inferred from a failure.

For each row: take the family `close()` would take first, walk the RAW machine,
and for every top string of width p record

  * the raw steps from that visit to the next family MEMBER (the fill's cost),
  * the same for a typical interior increment at the same width (the baseline).

Two widths give a ratio; three or more give a verdict.  `affine` means the
fill's cost grows no faster than the counter's own width, `exponential` means
it doubles with each new digit -- the second needs `powsum` in the count
language (RULE_LADDER.md sec.2), i.e. rung three, and no amount of arm search
reaches it.

Usage: fillcost.py --list rows.txt [--out costs.jsonl] [--steps 400000]
       fillcost.py --spec SPEC
"""

import argparse
import json
import os
import statistics
import sys
import time

from discover import build_ladder, mine_shapes
from engine import parse_tm
from trace import block_rle, simulate

import valfam as V

HERE = os.path.dirname(os.path.abspath(__file__))


def anchor_walk(fam, tm, steps):
    """[(raw t, digits or None, p)] at every anchor visit of the raw run."""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    out = []
    for t in range(steps):
        h = tape.get(pos, 0)
        if q == fam.q and h == fam.h:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            cfg = (q, h, block_rle(gl), block_rle(gr))
            pp = fam.far_p(cfg)
            if pp is not None:
                c = V.runs_cells(fam.counter_side(cfg))
                out.append((t, None if c is None else fam.decode(c), pp))
        tr = tm.get((q, h))
        if tr is None:
            break
        w, d, q = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
    return out


def verdict(fills):
    """[(p, steps)] -> one of affine / exponential / unknown.

    The test is the ratio between consecutive fills, normalized to one extra
    DIGIT (widths need not be consecutive -- a law that widens by two only
    ever visits one parity).  A per-digit ratio at or above 1.6 doubling-ish
    is exponential; near 1 is affine.  Fewer than two fills is no verdict."""
    if len(fills) < 2:
        return 'unknown', None
    rs = []
    for (p0, s0), (p1, s1) in zip(fills, fills[1:]):
        if p1 <= p0 or s0 <= 0:
            continue
        rs.append((s1 / s0) ** (1.0 / (p1 - p0)))
    if not rs:
        return 'unknown', None
    r = statistics.median(rs)
    return ('exponential' if r >= 1.6 else
            'affine' if r <= 1.25 else 'superlinear'), round(r, 3)


def measure(spec, steps=400000, trace=20000, ladder_cap=60.0, which=0):
    t0 = time.time()
    tm = parse_tm(spec)
    snaps = simulate(tm, trace)
    if snaps and snaps[-1][1] is None:
        return {'spec': spec, 'verdict': 'halts'}
    rules = build_ladder(tm, mine_shapes(snaps), time_cap=ladder_cap)
    fams = V.find_families(tm, snaps, rules)
    if not fams:
        return {'spec': spec, 'verdict': 'no family'}
    fam = fams[min(which, len(fams) - 1)][0]
    walk = anchor_walk(fam, tm, steps)
    dec = [(t, ds) for t, ds, _ in walk if ds]
    fills, inter = [], {}
    for i in range(len(dec) - 1):
        t, ds = dec[i]
        cost = dec[i + 1][0] - t
        if all(d == fam.b - 1 for d in ds):
            fills.append((len(ds), cost))
        else:
            inter.setdefault(len(ds), []).append(cost)
    v, r = verdict(fills)
    base = {p: int(statistics.median(c)) for p, c in sorted(inter.items())}
    bv, br = verdict([(p, s) for p, s in sorted(base.items())])
    return {'spec': spec, 'verdict': v, 'per_digit_ratio': r,
            'fills': fills, 'interior_median': base,
            'interior_verdict': bv, 'interior_ratio': br,
            'base': fam.b, 'anchor': chr(65 + fam.q) + str(fam.h),
            'decodable_visits': len(dec), 'seconds': round(time.time() - t0, 1)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--list')
    ap.add_argument('--out')
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--which', type=int, default=0)
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.split()[0] for l in open(a.list) if l.strip()]
    out = []
    for s in specs:
        try:
            r = measure(s, a.steps, which=a.which)
        except Exception as e:                             # noqa: BLE001
            r = {'spec': s, 'verdict': 'crash: %s' % type(e).__name__,
                 'detail': str(e)[:160]}
        out.append(r)
        print('%-32s %-12s ratio=%-6s fills=%s interior=%s'
              % (s, r['verdict'], r.get('per_digit_ratio'),
                 r.get('fills', [])[:5], r.get('interior_verdict')))
        sys.stdout.flush()
    if a.out:
        with open(a.out, 'w') as f:
            for r in out:
                f.write(json.dumps(r) + '\n')
    from collections import Counter
    print('\n== verdicts ==')
    for k, n in Counter(r['verdict'] for r in out).most_common():
        print('  %-14s %3d' % (k, n))


if __name__ == '__main__':
    main()
