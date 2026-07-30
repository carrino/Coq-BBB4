#!/usr/bin/env python3
"""UNTRUSTED probe: GROUP a row list by the canonical form of its sparse
state's avoid sub-machine, modulo state relabelling and mirroring.

This is the probe docs/REACHST_TIER.md section 7 says to run BEFORE costing a
flavour lemma.  Wave 1 sized its "third flavour" at two rows from the two rows
that had suggested it; run over the whole open core the same table turned out
to sit under 25, and its sibling under 9 more.  Grouping first is three lines
of work and it is the difference between a two-row lemma and a fifty-row one.

  python3 tools/reachst/cluster.py tools/closeout/core_rows.txt

Prints one block per distinct avoid table, largest first, with whether that
table terminates exhaustively over every tape of width <= 10 (a flavour lemma
is only worth writing when it does).  Nothing here carries proof weight.
"""
import itertools
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from avoid_probe import parse, usage, avoid_table, terminates, LAB   # noqa: E402


def mirror(t):
    return {k: (None if v is None else (v[0], -v[1], v[2])) for k, v in t.items()}


def render(t):
    return ' '.join(
        '%s%d->%s' % (LAB[q], s, 'HALT' if t[(q, s)] is None else
                      '%d%s%s' % (t[(q, s)][0], 'R' if t[(q, s)][1] > 0 else 'L',
                                  LAB[t[(q, s)][2]]))
        for (q, s) in sorted(t))


def canon(t):
    """Least render() over all relabellings of the table's live states, and
    over the mirror -- the ReachSt roles are section variables and
    Mirror.mirror_visits is an iff, so both are free."""
    live = sorted(set(q for (q, s) in t))
    best = None
    for tt in (t, mirror(t)):
        for perm in itertools.permutations(range(len(live))):
            m = {live[i]: perm[i] for i in range(len(live))}
            out, ok = {}, True
            for (q, s), v in tt.items():
                if v is None:
                    out[(m[q], s)] = None
                elif v[2] not in m:
                    ok = False
                    break
                else:
                    out[(m[q], s)] = (v[0], v[1], m[v[2]])
            if not ok:
                continue
            key = render(out)
            if best is None or key < best:
                best = key
    return best


def main():
    rows = open(sys.argv[1]).read().split()
    groups = defaultdict(list)
    for m in rows:
        c = usage(m, 200000)
        sp = min(range(4), key=lambda i: c[i])
        at = avoid_table(parse(m), sp)
        groups[canon(at)].append((m, LAB[sp], c[sp], at))
    for key, v in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        ok, _ = terminates(v[0][3], 10)
        print('=== %2d rows  terminates=%s   %s' % (len(v), ok, key))
        for m, sp, n, _ in v:
            print('      %s  sparse=%s (%d fires in 200k)' % (m, sp, n))
    print('\n%d rows in %d groups; %d groups terminate'
          % (len(rows), len(groups),
             sum(1 for v in groups.values() if terminates(v[0][3], 10)[0])))


main()
