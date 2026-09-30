#!/usr/bin/env python3
"""Non-firing run lengths on a TriGlue family graph (UNTRUSTED, diagnostics).

    python3 tools/closeouttr/ta/runlen.py DUMP.jsonl SPEC Q,H [--starts 2000] [--max 10**6]

Iterates TriGlue's own abstract map tnxt (walk the dispatch tree, jump to
the leaf's affine target) from random values in every family, and reports
the longest run of steps whose leaves do not fire instruction (Q,H), by
start size.  A run that never ends within the step cap is reported as such.
"""
import argparse
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ti_batch as T                            # noqa: E402
import ti_coq as C                              # noqa: E402


def step(cert, fi, vals):
    F = cert['fams'][fi]
    r = C.twalk(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'], vals)
    if r is None:
        return None
    l, R, z = r
    lf = cert['leaves'][l]
    return l, lf['g'], [C.aeval(z, e) for e in lf['tgt']]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('dump')
    ap.add_argument('spec')
    ap.add_argument('instr')
    ap.add_argument('--starts', type=int, default=2000)
    ap.add_argument('--cap', type=int, default=100000)
    ap.add_argument('--anchor', type=int, default=-1,
                    help='count only arrivals in this family (rounds), not steps')
    a = ap.parse_args()
    t = tuple(int(x) for x in a.instr.split(','))
    for line in open(a.dump):
        d = json.loads(line)
        if d['spec'] == a.spec and 'cert' in d:
            break
    cert = T.detuple(dict(d['cert'], ranks=[], S=[], P=1))
    fired = [set(map(tuple, f)) for f in d['fired']]
    rng = random.Random(1)
    for hi in (10, 100, 10 ** 3, 10 ** 4, 10 ** 6):
        worst, never = 0, 0
        for _ in range(a.starts):
            fi = rng.randrange(len(cert['fams']))
            vals = [rng.randrange(hi) for _ in range(cert['fams'][fi]['n'])]
            n = 0
            steps = 0
            while n < a.cap:
                r = step(cert, fi, vals)
                if r is None:
                    break
                l, fi, vals = r
                if t in fired[l]:
                    break
                steps = locals().get('steps', 0) + 1
                if a.anchor < 0 or fi == a.anchor:
                    n += 1
                if steps > a.cap * 50:
                    n = a.cap
                    break
            else:
                never += 1
            worst = max(worst, n)
        print('starts < %-8d longest non-firing run %d steps%s' % (
            hi, worst, ', %d never fire within %d' % (never, a.cap) if never else ''))


if __name__ == '__main__':
    main()
