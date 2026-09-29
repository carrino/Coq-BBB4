#!/usr/bin/env python3
"""Characterise class-DN rows (UNTRUSTED measurement, SCOPING_INSTR.md 7.4.DX).

    cc -O2 -o /tmp/dx_sim tools/closeouttr/dx_sim.c
    python3 tools/closeouttr/dx_char.py sample N SEED [--list ROWS] > sample.txt
    python3 tools/closeouttr/dx_char.py char sample.txt OUT.tsv [--sim /tmp/dx_sim]
            [--steps 100000000] [--jobs 4]

    python3 tools/closeouttr/dx_char.py junk ROWS OUT.tsv [--sim /tmp/dx_sim]

`sample` draws N rows of the open class-DN rows (classes.py order, fixed
seed), or of ROWS.  `char` runs each for STEPS steps with dx_sim and writes
one TSV line per row (resumable: rows already in OUT are skipped):

  w6 w7 w8   the visited extent at 1e6, 1e7, 1e8 steps
  exp        log(w8 / w6) / log(100): ~0.05 log counter, 1/3 sweep counter,
             1/2 bouncer, 1 translated / linear
  expL expR  the same exponent for each end separately (the distance of
             the leftmost / rightmost visited cell from the start cell)
  sides      L, R or LR: which ends of the extent still grew after 1e6
  gapratio   the median ratio of consecutive record gaps on the busier side
             (~1 with gaps growing by a constant: a bouncer; ~2 or 4: the
             records come once per doubling)
  sweeps     full edge-to-edge sweeps of the head, per record
  shape      from exp: log, cube, sqrt, lin, other
  kind       counter (log), sweepctr (cube), bouncer (sqrt, full sweeps),
             bouncer_part (sqrt, the head turns inside the extent), linear,
             other
  hybrid     for sqrt rows, the two ends: sqrt+log (a bouncer on one side,
             a counter on the other), sqrt+sqrt, sqrt+fix (one end never
             moves), or other
  tape       the period structure of the tape at the end: the periodic
             blocks of at least 16 cells, as period:word:length, in tape
             order; `junk` cells not in any block
"""
import argparse
import math
import os
import random
import statistics
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

COLS = ['spec', 'w6', 'w7', 'w8', 'exp', 'expL', 'expR', 'sides', 'gapratio',
        'sweeps', 'shape', 'kind', 'hybrid', 'nblocks', 'nwords', 'junk', 'blocks']


def cmd_sample(a):
    if a.list:
        rows = [l.split()[0] for l in open(a.list) if l.strip()]
    else:
        from classes import load
        remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
        rows = [s for s, c, _ in load() if c == 'DN' and s in remaining]
    random.seed(a.seed)
    for s in sorted(random.sample(rows, a.n)):
        print(s)


def canon(w):
    return min(w[k:] + w[:k] for k in range(len(w)))


def blocks(s, pmax=16, minlen=16):
    """greedy left-to-right cover by maximal periodic runs"""
    out, junk, i, n = [], 0, 0, len(s)
    while i < n:
        best = (0, 1)
        for p in range(1, pmax + 1):
            j = i + p
            while j < n and s[j] == s[j - p]:
                j += 1
            if j - i > best[0] and j - i >= 2 * p:
                best = (j - i, p)
        ln, p = best
        if ln >= minlen:
            out.append((p, canon(s[i:i + p]), ln))
            i += ln
        else:
            junk += 1
            i += 1
    return out, junk


def shape_of(e):
    if e is None:
        return 'none'
    if e < 0.15:
        return 'log'
    if 0.25 <= e < 0.42:
        return 'cube'
    if 0.42 <= e < 0.62:
        return 'sqrt'
    if 0.85 <= e < 1.15:
        return 'lin'
    return 'other'


def char_row(sim, spec, steps):
    out = subprocess.run([sim, spec, str(steps)], capture_output=True,
                         text=True).stdout.split('\n')
    X = {int(l.split()[1]): (int(l.split()[2]), int(l.split()[3]))
         for l in out if l.startswith('X ')}
    RL = [int(l.split()[2]) for l in out if l.startswith('R L')]
    RR = [int(l.split()[2]) for l in out if l.startswith('R R')]
    W = [int(l.split()[1]) for l in out if l.startswith('W ')][0]
    T = [l[2:] for l in out if l.startswith('T ')]
    end = [l.split() for l in out if l.startswith(('END', 'HALT', 'EDGE'))][0]
    r = dict(spec=spec)

    def w(k):
        x = X.get(10 ** k)
        return x[1] - x[0] + 1 if x else None
    r['w6'], r['w7'], r['w8'] = w(6), w(7), w(8)
    e = None
    if r['w6'] and r['w8']:
        e = math.log(r['w8'] / r['w6']) / math.log(100)
    r['exp'] = '%.3f' % e if e is not None else '-'
    es = {}
    if 10 ** 6 in X and 10 ** 8 in X:
        for side, a, b in (('L', -X[10 ** 6][0], -X[10 ** 8][0]),
                           ('R', X[10 ** 6][1], X[10 ** 8][1])):
            es[side] = (math.log(max(1, b) / max(1, a)) / math.log(100), b)
    for side in 'LR':
        r['exp' + side] = '%.3f' % es[side][0] if side in es else '-'
    sides = ''
    if 10 ** 6 in X and 10 ** 8 in X:
        if X[10 ** 8][0] < X[10 ** 6][0]:
            sides += 'L'
        if X[10 ** 8][1] > X[10 ** 6][1]:
            sides += 'R'
    r['sides'] = sides or '-'
    rec = RL if len(RL) >= len(RR) else RR
    rec = [x for x in rec if x > 10 ** 4]
    gaps = [rec[k + 1] - rec[k] for k in range(len(rec) - 1)]
    gr = [gaps[k + 1] / gaps[k] for k in range(len(gaps) - 1) if gaps[k] > 0][-20:]
    r['gapratio'] = '%.2f' % statistics.median(gr) if gr else '-'
    nrec = len(RL) + len(RR)
    r['sweeps'] = '%.2f' % (W / nrec) if nrec else '-'
    sh = shape_of(e)
    if end[0] != 'END':
        sh = end[0].lower()
    r['shape'] = sh
    kind = {'log': 'counter', 'cube': 'sweepctr', 'lin': 'linear'}.get(sh, 'other')
    if sh == 'sqrt':
        kind = 'bouncer' if nrec and W / nrec > 0.5 else 'bouncer_part'
    r['kind'] = kind

    def side_kind(ew):
        ex, wd = ew
        if wd < 3 or ex < 0.02:
            return 'fix'
        if ex < 0.15:
            return 'log'
        if 0.4 < ex < 0.6:
            return 'sqrt'
        return 'x%.1f' % ex
    r['hybrid'] = '-'
    if sh == 'sqrt' and len(es) == 2:
        k = sorted([side_kind(es['L']), side_kind(es['R'])])
        r['hybrid'] = {('log', 'sqrt'): 'sqrt+log', ('sqrt', 'sqrt'): 'sqrt+sqrt',
                       ('fix', 'sqrt'): 'sqrt+fix'}.get(tuple(k), 'other')
    if T:
        tape = T[0].replace('[', '').replace(']', '')
        tape = ''.join(c for c in tape if c in '01')
        bl, junk = blocks(tape)
        r['nblocks'] = len(bl)
        r['nwords'] = len(set(b[1] for b in bl))
        r['junk'] = junk
        r['blocks'] = ' '.join('%d:%s:%d' % b for b in bl) or '-'
    else:
        r['nblocks'] = r['nwords'] = r['junk'] = '-'
        r['blocks'] = 'wide'
    return r


JCOLS = ['spec', 'w6', 'w8', 'j6', 'j7', 'j8', 'jexp', 'segs', 'longest', 'ends', 'lp6', 'lp7', 'lp8',
         'lcov', 'jclass']


def junk_segments(s, pmax=16, minlen=16):
    """the maximal runs of cells no periodic block covers, as (start, len)"""
    segs, i, n = [], 0, len(s)
    cur = None
    while i < n:
        best = (0, 1)
        for p in range(1, pmax + 1):
            j = i + p
            while j < n and s[j] == s[j - p]:
                j += 1
            if j - i > best[0] and j - i >= 2 * p:
                best = (j - i, p)
        ln, p = best
        if ln >= minlen:
            if cur:
                segs.append(tuple(cur))
                cur = None
            i += ln
        else:
            if cur is None:
                cur = [i, 0]
            cur[1] += 1
            i += 1
    if cur:
        segs.append(tuple(cur))
    return segs


def long_periods(s, segs, pmax=64):
    """cover the segments [segs] of [s] by periodic runs of period
    17..pmax (at least two periods long): (the heaviest such period, the
    fraction of the segments' cells such runs cover)"""
    wt, cov, tot = {}, 0, 0
    for (a, ln) in segs:
        tot += ln
        i, end = a, a + ln
        while i < end:
            best = (0, 0)
            for p in range(17, pmax + 1):
                j = i + p
                while j < end and s[j] == s[j - p]:
                    j += 1
                if j - i >= 2 * p and j - i > best[0]:
                    best = (j - i, p)
            if best[0]:
                wt[best[1]] = wt.get(best[1], 0) + best[0]
                cov += best[0]
                i += best[0]
            else:
                i += 1
    top = max(wt, key=wt.get) if wt else 0
    return top, (cov / tot if tot else 0.0)


def junk_row(sim, spec):
    """the junk (cells in no periodic block) at 1e6, 1e7, 1e8 steps: how
    fast it grows and where it sits.  jclass:
      edge_log   the junk grows like a counter (exponent < 0.2) and sits in
                 at most two segments at the tape's ends: a bouncer with a
                 counter at its edge (the hybrids of 7.4.DX / HY)
      inner_log  counter-like growth, but inside the tape (a counter
                 between two growing blocks: HY's two-sided glue)
      longper    the junk is not a counter, and the tape is mostly
                 (>= 60%) periodic with a period 17..64 that is the same at
                 1e7 and 1e8: a bouncer whose block is longer than the
                 block detector's 16 cells (often a level-2 word
                 A (011)^k with k fixed)
      nested     the same, but the long period changes between 1e7 and
                 1e8: blocks of the form (A B^k)^n with k growing, a bouncer
                 inside a bouncer
      spread     the junk grows with the extent (exponent >= 0.35) and is
                 not long-periodic: irregular (Fibonacci-like); no landed
                 route
      other      in between"""
    r = dict(spec=spec)
    J = {}
    for k in (6, 7, 8):
        out = subprocess.run([sim, spec, str(10 ** k)], capture_output=True, text=True).stdout.split('\n')
        T = [l[2:] for l in out if l.startswith('T ')]
        if not T:
            return None
        tape = ''.join(c for c in T[0] if c in '01')
        J[k] = (len(tape), junk_segments(tape), tape)
    w6, w8 = J[6][0], J[8][0]
    js = {k: sum(ln for _, ln in J[k][1]) for k in J}
    r['w6'], r['w8'] = w6, w8
    r['j6'], r['j7'], r['j8'] = js[6], js[7], js[8]
    e = math.log(max(js[8], 1) / max(js[6], 1)) / math.log(100)
    r['jexp'] = '%.2f' % e
    segs = [sg for sg in J[8][1] if sg[1] >= 4]
    r['segs'] = len(segs)
    r['longest'] = max((ln for _, ln in segs), default=0)
    edge = w8 // 20
    ends = [sg for sg in segs if sg[0] <= edge or sg[0] + sg[1] >= w8 - edge]
    r['ends'] = len(ends)
    lp = {k: long_periods(J[k][2], [(0, J[k][0])]) for k in J}
    r['lp6'], r['lp7'], r['lp8'] = lp[6][0], lp[7][0], lp[8][0]
    r['lcov'] = '%.2f' % lp[8][1]
    if e < 0.2:
        r['jclass'] = 'edge_log' if len(segs) <= 2 and len(ends) == len(segs) else 'inner_log'
    elif lp[8][1] >= 0.6:
        r['jclass'] = 'longper' if lp[7][0] == lp[8][0] else 'nested'
    elif e >= 0.35:
        r['jclass'] = 'spread'
    else:
        r['jclass'] = 'other'
    return r


def cmd_junk(a):
    rows = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    with open(a.out, 'w') as o, ThreadPoolExecutor(a.jobs) as ex:
        o.write('# ' + '\t'.join(JCOLS) + '\n')
        for r in ex.map(lambda s: junk_row(a.sim, s), rows):
            if r:
                o.write('\t'.join(str(r[c]) for c in JCOLS) + '\n')
                o.flush()


def cmd_char(a):
    done = set()
    if os.path.exists(a.out):
        done = set(l.split('\t')[0] for l in open(a.out))
    todo = [l.split()[0] for l in open(a.sample) if l.strip() and l.split()[0] not in done]
    new = not os.path.exists(a.out)
    with open(a.out, 'a') as o, ThreadPoolExecutor(a.jobs) as ex:
        if new:
            o.write('# ' + '\t'.join(COLS) + '\n')
        for r in ex.map(lambda s: char_row(a.sim, s, a.steps), todo):
            o.write('\t'.join(str(r[c]) for c in COLS) + '\n')
            o.flush()


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('sample')
    s.add_argument('n', type=int)
    s.add_argument('seed', type=int)
    s.add_argument('--list')
    c = sub.add_parser('char')
    c.add_argument('sample')
    c.add_argument('out')
    c.add_argument('--sim', default='/tmp/dx_sim')
    c.add_argument('--steps', type=int, default=10 ** 8)
    c.add_argument('--jobs', type=int, default=2)
    j = sub.add_parser('junk', help='where the junk of ROWS sits and how fast it grows (7.4.MB)')
    j.add_argument('rows')
    j.add_argument('out')
    j.add_argument('--sim', default='/tmp/dx_sim')
    j.add_argument('--jobs', type=int, default=2)
    a = ap.parse_args()
    {'sample': cmd_sample, 'char': cmd_char, 'junk': cmd_junk}[a.cmd](a)


if __name__ == '__main__':
    main()
