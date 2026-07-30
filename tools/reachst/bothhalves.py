#!/usr/bin/env python3
"""UNTRUSTED probe: for each row and each state q, do BOTH halves of a
REACHST board exist?

A board lifts ONE state q out of the closure and proves its liveness as a
[ReachSt] theorem, so it needs two independent things:

  T   the q-avoiding sub-machine TERMINATES exhaustively (every tape of
      width <= 10, every head position, every start state)
  N   NGramHist discharges the OTHER THREE states with q lifted out
      (tools/nghist/reachst_prove.prove_ext, k=2 then k=3, n=2)

Output is one cell per state, e.g. `A:T- B:fN C:T- D:T-`: there only B can be
lifted by the closure and only B's avoid machine fails to terminate, so no
choice of q works and the row is out of the tier's reach entirely.  A row is
boardable as soon as some state reads `TN`, whatever flavour its avoid table
turns out to be -- though emitting the board still needs a NAMED flavour
lemma in theories/Checkers/ReachSt.v, which is what cluster.py sizes.

  python3 tools/reachst/bothhalves.py tools/closeout/core_rows.txt

Nothing here carries proof weight; the Coq kernel re-checks every board.
"""
import os
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'tools/nghist'))
sys.path.insert(0, os.path.join(ROOT, 'tools/reachst'))

import reachst_prove as RP                                          # noqa: E402
from avoid_probe import parse, avoid_table, terminates, show, LAB    # noqa: E402

KN = [(2, 2), (3, 2)]


def main():
    rows = open(sys.argv[1]).read().split()
    cache = {}
    cands = []
    for m in rows:
        tab = parse(m)
        if any(v is None for v in tab.values()):
            print('%s  (undefined transition -- boards via its completions)' % m)
            sys.stdout.flush()
            continue
        cells, hit = [], []
        for qi in range(4):
            key = show(avoid_table(tab, qi))
            if key not in cache:
                cache[key] = terminates(avoid_table(tab, qi), 10)[0]
            t = cache[key]
            ok = any(RP.prove_ext(m, k, n, 200, 40000, qext=LAB[qi])[0] is not None
                     for (k, n) in KN)
            cells.append('%s:%s%s' % (LAB[qi], 'T' if t else 'f', 'N' if ok else '-'))
            if t and ok:
                hit.append((LAB[qi], key))
        print('%s  %s  %s' % (m, ' '.join(cells),
                              'BOARDABLE ' + ','.join(q for q, _ in hit) if hit else ''))
        sys.stdout.flush()
        cands += [(m, q, key) for q, key in hit]
    print('\n%d of %d rows have a state with BOTH halves'
          % (len(set(m for m, _, _ in cands)), len(rows)))
    g = defaultdict(list)
    for m, q, key in cands:
        g[key].append((m, q))
    for key, v in sorted(g.items(), key=lambda kv: -len(kv[1])):
        print('  %2d rows  %s' % (len(v), key))
        for m, q in v:
            print('        %s  avoid=%s' % (m, q))


main()
