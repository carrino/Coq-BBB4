#!/usr/bin/env python3
"""Characterise the hybrid rows the finder does not certify (UNTRUSTED
measurement, SCOPING_INSTR.md 7.4.HY).

    python3 tools/closeouttr/hy_residue.py ROWS.txt > residue.txt

For each row: the tape at the last far-side record before 4e5 steps (so a
sweep is complete and the block reads uniformly), cut into blocks (runs of
a unit of at most 4 cells over at least 8 repetitions).  Reports the width,
the number of blocks, of long blocks (over 40 cells), the longest, the units
of the long blocks and which side grew in the second half.
"""
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hy_batch as H  # noqa: E402


def tape_at(spec, N):
    tab = H.parse(spec)
    tape = bytearray(40000)
    pos = 20000
    q = 0
    lo = hi = pos
    recs = []
    snap = None
    for t in range(N):
        h = tape[pos]
        w, d, nq = tab[(q, h)]
        tape[pos] = w
        pos += d
        q = nq
        if pos > hi:
            hi = pos
            recs.append((t, 'R'))
            if t > N - N // 8:
                snap = (lo, hi, bytes(tape))
        if pos < lo:
            lo = pos
            recs.append((t, 'L'))
            if t > N - N // 8:
                snap = (lo, hi, bytes(tape))
    if snap is None:
        snap = (lo, hi, bytes(tape))
    lo, hi, tp = snap
    return tp[lo:hi + 1].decode('latin1').translate({0: '0', 1: '1'}), recs


def blocks(s):
    out = []
    i = 0
    while i < len(s):
        best = None
        for u in (1, 2, 3, 4):
            U = s[i:i + u]
            n = 0
            while s[i + n * u:i + (n + 1) * u] == U:
                n += 1
            if n >= 8 and (best is None or n * u > best[1]):
                best = (U, n * u)
        if best:
            out.append(best)
            i += best[1]
        else:
            i += 1
    return out


def char(spec, N=400000):
    s, recs = tape_at(spec, N)
    bl = blocks(s)
    late = [r for r in recs if r[0] > N // 2]
    return dict(width=len(s), nblocks=len(bl), nlong=sum(1 for b in bl if b[1] > 40),
                longest=max((b[1] for b in bl), default=0),
                units=sorted(set(b[0] for b in bl if b[1] > 40))[:4],
                sides=dict(collections.Counter(r[1] for r in late)))


if __name__ == '__main__':
    for line in open(sys.argv[1]):
        spec = line.split()[0]
        print(spec, json.dumps(char(spec)))
