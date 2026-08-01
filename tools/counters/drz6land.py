#!/usr/bin/env python3
"""UNTRUSTED (tools/): look for a DENSE landmark family for Drozd's sixth row.

`LapGlueNeverIx.glue_neverqh_ix` takes an ARBITRARY index type, so the anchor
family need not be the sparse `R(k)`.  If some (state, symbol[, shape]) class
recurs with a BOUNDED gap, each lap is a bounded computation and the whole
exponential blow-up is carried by the index instead of by an inner induction.

    python3 tools/counters/drz6land.py [--steps N]
"""
import argparse
from collections import defaultdict

SPEC = "1RB0RD_1LB1LC_1RC0RA_0LB1RD"
LAB = "ABCD"
from drz6lap import parse, run


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=300000)
    a = ap.parse_args()
    ev = list(run(SPEC, a.steps))
    n = len(ev)
    print("steps %d" % n)
    print("  gaps between consecutive visits, per (state, symbol):")
    for st in range(4):
        for sym in range(2):
            ns = [k for k, s, y, L, R in ev if s == st and y == sym]
            if not ns:
                print("    %s%d : never" % (LAB[st], sym))
                continue
            g = [b - c for c, b in zip(ns, ns[1:])]
            print("    %s%d : visits %-7d  maxgap %-8d  gapset %s"
                  % (LAB[st], sym, len(ns), max(g) if g else 0,
                     sorted(set(g))[:12]))
    # right-run length at each visit, for the promising ones
    print("  refine by right-run length r (state,sym,r) -> maxgap:")
    for st in range(4):
        for sym in range(2):
            byr = defaultdict(list)
            for k, s, y, L, R in ev:
                if s == st and y == sym:
                    byr[len(R)].append(k)
            worst = 0
            for r, ns in byr.items():
                g = [b - c for c, b in zip(ns, ns[1:])]
                worst = max(worst, max(g) if g else 0)
            print("    %s%d : %d distinct r, worst intra-r gap %d"
                  % (LAB[st], sym, len(byr), worst))


if __name__ == '__main__':
    main()
