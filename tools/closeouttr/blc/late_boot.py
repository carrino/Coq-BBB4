#!/usr/bin/env python3
"""bl_ti.py (TriGlueTr on exponent lattices) with LATE boots (200,000 and
1,000,000 steps): the finder of SCOPING_INSTR.md §7.4.BLC that boarded the
15th QH hybrid.  UNTRUSTED; resumable (rows already in OUT are skipped).

    python3 tools/closeouttr/blc/late_boot.py ROWS.txt OUT.jsonl [--jobs 2] [--timeout 300]
"""
import argparse
import json
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import bl_ti as B                               # noqa: E402

T = B.T


def one(args):
    spec, timeout = args
    B.install()
    T.MAXLEAF, T.MAXSTEPS = 3000, 20000
    B.TLIST = (200000, 1000000)
    return T.find(spec, timeout, 'DN', 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--timeout', type=int, default=300)
    a = ap.parse_args()
    specs = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(one, todo):
            f.write(json.dumps(T.jsonable(r)) + '\n')
            f.flush()
            print(r['spec'], r.get('err', 'OK')[:120], flush=True)


if __name__ == '__main__':
    main()
