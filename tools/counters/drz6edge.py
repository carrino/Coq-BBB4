#!/usr/bin/env python3
"""UNTRUSTED (tools/): list the LEFT-EDGE events of Drozd's sixth row --
every configuration whose head sits within `--pos` cells of the left wall --
so the macro trajectory of the second half-lap can be read off.

    python3 tools/counters/drz6edge.py --k0 7 --k1 10 --pos 6
"""
import argparse
from collections import defaultdict

SPEC = "1RB0RD_1LB1LC_1RC0RA_0LB1RD"
LAB = "ABCD"
from drz6lap import parse


def run(spec, T):
    tab = parse(spec)
    tape = defaultdict(int)
    pos, st, lo, hi = 0, 0, 0, 0
    for n in range(T):
        sym = tape[pos]
        L = [tape[x] for x in range(lo, pos)][::-1]
        R = [tape[x] for x in range(pos + 1, hi + 1)]
        while L and L[-1] == 0:
            L.pop()
        while R and R[-1] == 0:
            R.pop()
        yield (n, st, sym, tuple(L), tuple(R), pos)
        e = tab[(st, sym)]
        if e is None:
            return
        w, d, ns = e
        tape[pos] = w
        lo, hi = min(lo, pos), max(hi, pos)
        pos += d
        st = ns
        lo, hi = min(lo, pos), max(hi, pos)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k0', type=int, default=7)
    ap.add_argument('--k1', type=int, default=10)
    ap.add_argument('--pos', type=int, default=6)
    ap.add_argument('--steps', type=int, default=300000)
    a = ap.parse_args()
    ev = list(run(SPEC, a.steps))
    hits = [(n, len(R)) for n, st, sym, L, R, p in ev
            if st == 2 and sym == 0 and not L and all(x == 1 for x in R)]
    n0 = [n for n, k in hits if k == a.k0][0]
    n1 = [n for n, k in hits if k == a.k1][0]
    print("R(%d)@%d -> R(%d)@%d   (%d steps);  head within %d of the wall:"
          % (a.k0, n0, a.k1, n1, n1 - n0, a.pos))
    prev = None
    for n, st, sym, L, R, p in ev[n0:n1 + 1]:
        if p <= a.pos:
            d = "" if prev is None else "  +%d" % (n - prev)
            prev = n
            print("%8d  pos=%d  %s  %-12s [%d] 1^%-6d %s%s"
                  % (n - n0, p, LAB[st], ''.join(map(str, reversed(L))), sym,
                     len(R), "" if all(x == 1 for x in R) else "NON-UNARY", d))


if __name__ == '__main__':
    main()
