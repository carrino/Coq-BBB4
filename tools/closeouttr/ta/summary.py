#!/usr/bin/env python3
"""Summarise TriNuTr certificates (UNTRUSTED, reporting only).

    python3 tools/closeouttr/ta/summary.py DUMP.jsonl NU.jsonl > summary.tsv

Per certified row: P, the number of families, and per instruction whose
liveness needs the l-adic part: l, K (the number of lexicographic
rankings) and the ratios E'/E on the non-firing edges other than 1, i.e.
the multiplier of the non-firing round (3/2 for the Collatz-like x -> 3x/2
branch).  Rows the finder did not certify are listed with its error.
"""
import collections
import json
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
import nu_find as N                              # noqa: E402
import ti_batch as T                             # noqa: E402
import ti_coq as C                               # noqa: E402

NAMES = 'ABCD'


def main():
    dumps = {}
    for line in open(sys.argv[1]):
        d = json.loads(line)
        if d.get('verdict') == 'norank':
            dumps.setdefault(d['spec'], d)
    print('# spec\tP\tfams\tinstr: l K ratios (non-firing edges, != 1)')
    for line in open(sys.argv[2]):
        c = json.loads(line)
        if 'err' in c:
            print('%s\t-\t-\tFAIL %s' % (c['spec'], c['err'][:120]))
            continue
        d = dumps[c['spec']]
        cert = T.detuple(dict(d['cert'], ranks=[], S=[], P=1))
        pins = set(map(tuple, cert['pins']))
        tab = T.parse(c['spec'])
        if cert['mir']:
            tab = T.mirror(tab)
        tabw = {k: (None if k in pins else v) for k, v in tab.items()}
        fired = [set(map(tuple, f)) for f in d['fired']]
        P = c['P']
        S = [(l, tuple(r)) for l, r in c['S']]
        parts = []
        for t, (ell, K, rows) in c['live']:
            t = tuple(t)
            if all(E[0] == 1 and not any(E[1]) for _, E, _ in rows):
                if K > 1:
                    parts.append('%s%d: K=%d' % (NAMES[t[0]], t[1], K))
                continue
            rs = collections.Counter()
            for i, nd in enumerate(S):
                if t in fired[nd[0]]:
                    continue
                for s, src, tgt, rho2, cands in T.edges(cert, P, tabw, nd):
                    for l2 in cands:
                        if t in fired[l2]:
                            continue
                        i2 = S.index((l2, rho2))
                        if rows[i2][0] != rows[i][0]:
                            continue
                        r = N.ratio(N.eval_lin([Fr(rows[i][1][0])] + [Fr(x) for x in rows[i][1][1]], src),
                                    N.eval_lin([Fr(rows[i2][1][0])] + [Fr(x) for x in rows[i2][1][1]], tgt))
                        if r is not None and r != 1:
                            rs[str(r)] += 1
            parts.append('%s%d: l=%d K=%d r={%s}' % (NAMES[t[0]], t[1], ell, K,
                                                     ','.join(sorted(rs))))
        print('%s\t%d\t%d\t%s' % (c['spec'], P, len(cert['fams']), '; '.join(parts)))


if __name__ == '__main__':
    main()
