#!/usr/bin/env python3
"""UNTRUSTED: what NUMBER SYSTEM is the counter in?

No ladder, no decoding, no alphabet: count the DISTINCT counter-side cell
strings of each length at the busiest anchor whose far side is constant.  The
size of each length class is a fingerprint of the arithmetic --

    base-b positional   (b-1) * b^(n-1) strings of length n   ratio b
    Fibonacci / rank    F(n)                                  ratio 1.618

-- so a counter whose successor is not positional shows up before any reader is
written for it, and cannot be mistaken for a searcher that has not looked hard
enough.  That distinction is what this file exists to make: `valfam.py` reads a
base-b odometer, and a row it cannot read is either a gap in the search or an
arithmetic outside the model, with completely different consequences for the
plan.  See docs/LADDER_PLAN.md sec.4e.

Usage: numsys.py rows.txt
"""

import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from engine import parse_tm                                     # noqa: E402
from trace import simulate                                      # noqa: E402
import valfam as V                                              # noqa: E402


def classes(spec, steps=20000, min_visits=40, top_anchors=8):
    """Best anchor's length -> number of distinct counter strings."""
    tm = parse_tm(spec)
    snaps = simulate(tm, steps)
    byqh = collections.defaultdict(list)
    for t, s in snaps:
        if s is None:
            break
        byqh[(s[0], s[1])].append(s)
    best = None
    for (q, h), occ in sorted(byqh.items(), key=lambda kv: -len(kv[1]))[
            :top_anchors]:
        for side in ('L', 'R'):
            far = [tuple(V.runs_cells(s[3] if side == 'L' else s[2]) or ())
                   for s in occ]
            pop = collections.Counter(far)
            f0, n = pop.most_common(1)[0]
            if n < min_visits:
                continue
            ctr = [tuple(V.runs_cells(s[2] if side == 'L' else s[3]) or ())
                   for s, ff in zip(occ, far) if ff == f0]
            bylen = collections.defaultdict(set)
            for x in ctr:
                bylen[len(x)].add(x)
            counts = [(k, len(bylen[k])) for k in sorted(bylen) if k > 0][:12]
            if len(counts) < 4:
                continue
            step = counts[1][0] - counts[0][0]
            rat = [c2 / c1 for (k1, c1), (k2, c2) in zip(counts, counts[1:])
                   if c1 and k2 == k1 + step]
            if not rat:
                continue
            if best is None or n > best[0]:
                best = (n, '%s%d/%s' % (chr(65 + q), h, side), counts, rat)
    return best


def label(rat):
    m = sorted(rat)[len(rat) // 2]
    if 1.9 < m < 2.1:
        return 'base-2'
    if 2.8 < m < 3.2:
        return 'base-3'
    if 1.55 < m < 1.72:
        return 'FIBONACCI'
    return 'other %.2f' % m


def main():
    for spec in [l.split()[0] for l in open(sys.argv[1]) if l.strip()]:
        b = classes(spec)
        if b is None:
            print('%-30s no constant-far-side anchor' % spec)
        else:
            n, anchor, counts, rat = b
            print('%-30s %-7s vis=%-4d %-11s classes=%s'
                  % (spec, anchor, n, label(rat),
                     ' '.join('%d:%d' % c for c in counts[:9])))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
