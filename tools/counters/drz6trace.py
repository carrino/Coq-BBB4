#!/usr/bin/env python3
"""UNTRUSTED (tools/): dump the trajectory of Drozd's sixth row between two
`R(k)` anchors, in `cconf` coordinates, so the macro rules can be read off.

    python3 tools/counters/drz6trace.py --from 6 --to 7
"""
import argparse
from drz6lap import SPEC, LAB, run


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k0', type=int, default=6)
    ap.add_argument('--k1', type=int, default=7)
    ap.add_argument('--steps', type=int, default=300000)
    ap.add_argument('--max', type=int, default=400)
    a = ap.parse_args()
    ev = list(run(SPEC, a.steps))
    hits = [n for n, st, sym, L, R in ev
            if st == 2 and sym == 0 and not L and all(x == 1 for x in R)]
    ks = [len(R) for n, st, sym, L, R in ev
          if st == 2 and sym == 0 and not L and all(x == 1 for x in R)]
    n0 = hits[ks.index(a.k0)]
    n1 = hits[ks.index(a.k1)]
    print("R(%d) at n=%d  ->  R(%d) at n=%d   (%d steps)"
          % (a.k0, n0, a.k1, n1, n1 - n0))
    for n, st, sym, L, R in ev[n0:min(n1 + 1, n0 + a.max)]:
        print("%6d  %s  %-38s [%d] %s"
              % (n - n0, LAB[st],
                 ''.join(map(str, reversed(L))), sym,
                 ''.join(map(str, R))))


if __name__ == '__main__':
    main()
