#!/usr/bin/env python3
"""BL residue classifier (UNTRUSTED measurement, SCOPING_INSTR.md §7.4.BL).

    cc -O2 -o /tmp/bl_sim tools/closeouttr/bl/bl_sim.c
    python3 tools/closeouttr/bl/classify.py ROWS.txt [--sim /tmp/bl_sim] > OUT.tsv

Per row:
  * the rarest instruction that fires at least 4 times in 1e8 steps, and
    whether the ratios of its successive fire intervals are REGULAR (the last
    five within a factor 1.3 of each other: a round of fixed shape repeated,
    x2 / x4 per round), IRREGULAR (a Collatz-like round map: the fire depends
    on a residue the next round scrambles) or too FEW fires to tell;
  * the number of blocks (maximal runs of >= 3 copies of a unit of 1-6 cells)
    at the rare fire nearest 1e6 and nearest 6.4e7 steps: GROW if it rises
    by 2 or more (a list of blocks: a block-list numeration), else FLAT.
"""
import argparse
import subprocess
import sys
from multiprocessing import Pool

SIM = '/tmp/bl_sim'


def fires(spec, lim, snaps=()):
    out = subprocess.run([SIM, spec, str(lim)] + [str(t) for t in snaps],
                         capture_output=True, text=True).stdout
    res, tapes = {}, {}
    for l in out.split('\n'):
        p = l.split()
        if p and p[0] == 'T':
            tapes[int(p[1])] = p[2] if len(p) > 2 else ''
        elif p:
            res[p[0]] = [int(x) for x in p[1:]]
    return res, tapes


def regularity(ts):
    ts = [t for t in ts if t > 2000]
    if len(ts) < 4:
        return 'few'
    iv = [b - a for a, b in zip(ts, ts[1:])]
    rs = [iv[i + 1] / iv[i] for i in range(len(iv) - 1) if iv[i] > 0][-5:]
    if not rs or min(rs) <= 0:
        return 'few'
    return 'reg' if max(rs) / min(rs) < 1.3 else 'irr'


def nblocks(s):
    i, n = 0, 0
    while i < len(s):
        best = 0
        for p in range(1, 7):
            u = s[i:i + p]
            if len(u) < p:
                break
            k = 1
            while s[i + k * p:i + (k + 1) * p] == u:
                k += 1
            if k >= 3 and k * p > best:
                best = k * p
        if best:
            n += 1
            i += best
        else:
            i += 1
    return n


def one(spec):
    f, _ = fires(spec, 100000000)
    cand = [(len(v), k, v) for k, v in f.items() if len(v) >= 4]
    if cand:
        n, rare, ts = min(cand)
        reg = regularity(ts)
        snaps = [min(ts, key=lambda x: abs(x - target)) for target in (1000000, 64000000)]
    else:
        # every instruction fires 64+ times (a sweep-rate rare instruction):
        # fixed snapshot times
        rare, reg = 'sweep', 'sweep'
        snaps = [1000000, 64000000]
    _, tapes = fires(spec, max(snaps) + 1, snaps)
    b = [nblocks(tapes[t]) if t in tapes else -1 for t in snaps]
    grow = '-' if -1 in b else ('grow' if b[1] - b[0] >= 2 else 'flat')
    return spec, rare, reg, b[0], b[1], grow


def main():
    global SIM
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('--sim', default=SIM)
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    SIM = a.sim
    rows = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    print('# spec\trare\tfires\tblocks_a\tblocks_b\tlist')
    with Pool(a.jobs) as p:
        for r in p.imap(one, rows):
            print('\t'.join(map(str, r)), flush=True)


if __name__ == '__main__':
    main()
