#!/usr/bin/env python3
"""Characterise class-SP rows: the bursts of the rarest instruction
(UNTRUSTED measurement, SCOPING_INSTR.md 7.4.SP).

    cc -O2 -o /tmp/sp_burst tools/closeouttr/sp_burst.c
    python3 tools/closeouttr/sp_char.py sample N SEED > sample.txt
    python3 tools/closeouttr/sp_char.py char sample.txt [--burst /tmp/sp_burst]
            [--steps 100000000] [--json OUT]

`sample` draws N class-SP rows (fixed seed) and names each one's rarest
instruction: the fired instruction with the earliest last fire in the 1e8
scan (censustr_v9_scan_1e8.txt), which is how classes.py put the row in SP.
`char` re-runs each row with sp_burst and reports, for that instruction:

  fires   how often it fires in STEPS steps
  edge    every fire is at the visited extent's edge (the head on the
          leftmost or rightmost cell visited so far): the instruction is
          the one that grows the tape
  bursts  fires grouped when closer than max(1000, 1% of the step)
  ratio   the mean ratio of the last three burst starts (the geometric
          period growth: 2 = a binary counter's overflow, 4 = a bouncer
          whose sweep length doubles per phase)
  width   the visited extent at the end (log counters stay under ~100
          cells at 1e8; the doubling bouncers reach 10^4)
"""
import argparse
import collections
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SCAN = os.path.join(REPO, 'censustr_v9_scan_1e8.txt')
INS = ['A0', 'A1', 'B0', 'B1', 'C0', 'C1', 'D0', 'D1']


def rarest(parts):
    fr = [(i, int(t.split(':')[1]), int(t.split(':')[2]))
          for i, t in enumerate(parts[1:9])]
    fr = [x for x in fr if x[1] > 0]
    return min(fr, key=lambda x: x[2])


def cmd_sample(a):
    sys.path.insert(0, HERE)
    from classes import load
    rows = [s for s, c, _ in load() if c == 'SP']   # classes.py order
    random.seed(a.seed)
    pick = set(random.sample(rows, a.n))
    for line in open(SCAN):
        p = line.split()
        if p[0] in pick:
            i, cnt, last = rarest(p)
            print(p[0], i, cnt, last)


def ratio_class(x):
    if x is None:
        return '?'
    for v in (1.41, 2, 2.25, 4, 9):
        if abs(x - v) < 0.1 * v:
            return str(v)
    return 'other'


def char_row(burst, spec, instr, steps):
    out = subprocess.run([burst, spec, str(instr), str(steps), '0'],
                         capture_output=True, text=True).stdout.split('\n')
    F = [l.split() for l in out if l.startswith('F')]
    end = [l.split() for l in out if l.startswith(('END', 'HALT', 'EDGE'))][0]
    t = [int(f[1]) for f in F]
    pos = [int(f[2]) for f in F]
    lo = [int(f[3]) for f in F]
    hi = [int(f[4]) for f in F]
    edge = sum(1 for k in range(len(F)) if pos[k] in (lo[k], hi[k]))
    bursts = []
    for x in t:
        if bursts and x - bursts[-1][-1] < max(1000, 0.01 * x):
            bursts[-1].append(x)
        else:
            bursts.append([x])
    st = [b[0] for b in bursts if b[0] > 10000]
    r = [st[k + 1] / st[k] for k in range(len(st) - 1)][-3:]
    ratio = round(sum(r) / len(r), 2) if r else None
    width = int(end[3]) - int(end[2]) if end[0] == 'END' else None
    return dict(spec=spec, instr=INS[instr], fires=len(F), edge=edge,
                all_edge=bool(F) and edge == len(F), bursts=len(bursts),
                last_burst_sizes=[len(b) for b in bursts[-4:]],
                ratio=ratio, ratio_class=ratio_class(ratio), width=width)


def cmd_char(a):
    res = []
    for line in open(a.sample):
        spec, i = line.split()[:2]
        r = char_row(a.burst, spec, int(i), a.steps)
        res.append(r)
        print('%-28s %s fires %-8d edge %-8d bursts %-3d ratio %-6s width %s'
              % (spec, r['instr'], r['fires'], r['edge'], r['bursts'],
                 r['ratio'], r['width']), flush=True)
    C = collections.Counter
    print('# rows', len(res))
    print('# width < 200 (log):', sum(1 for r in res if r['width'] is not None and r['width'] < 200),
          ' width >= 1000:', sum(1 for r in res if r['width'] is not None and r['width'] >= 1000))
    print('# every fire at the extent edge:', sum(r['all_edge'] for r in res),
          ' some:', sum(1 for r in res if r['edge'] and not r['all_edge']),
          ' none:', sum(1 for r in res if not r['edge']))
    print('# period ratio:', dict(C(r['ratio_class'] for r in res)))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('sample')
    s.add_argument('n', type=int)
    s.add_argument('seed', type=int)
    c = sub.add_parser('char')
    c.add_argument('sample')
    c.add_argument('--burst', default='/tmp/sp_burst')
    c.add_argument('--steps', type=int, default=10 ** 8)
    c.add_argument('--json')
    a = ap.parse_args()
    cmd_sample(a) if a.cmd == 'sample' else cmd_char(a)


if __name__ == '__main__':
    main()
