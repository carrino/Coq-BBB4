#!/usr/bin/env python3
"""UNTRUSTED: print the space-time diagram in ABSOLUTE tape coordinates.

Every other dump in this directory is HEAD-RELATIVE, which is exactly the
wrong frame for reading a claim about which side of a bit its marker sits
on: a head-relative word shifts whenever the head does, so the same tape
reads as marker-before at one phase and marker-after at another.  A claim
like "1's to the LEFT of the bits when the msb is even, to the RIGHT when
it is odd" is a statement about COLUMN PARITY, and only an absolute-
coordinate dump can confirm or refute it.

Rows are steps, columns are tape cells, the head is shown in place.
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from emit_interleave import parse                                  # noqa: E402
import lapcert as LC                                               # noqa: E402

LAB = 'ABCD'


def run(spec, t0, t1, every, lo, hi, marks, rests=False):
    tab = parse(spec)
    cfg = (0, (), 0, ())
    pos = 0
    tape = {}
    out = []
    for t in range(t1 + 1):
        q, l, h, r = cfg
        tape[pos] = h
        keep = (h == 0) if rests else ((t - t0) % every == 0)
        if t >= t0 and keep:
            lo2 = lo if lo is not None else min(tape)
            hi2 = hi if hi is not None else max(tape)
            row = ''.join(('%d' % tape.get(i, 0)) for i in range(lo2, hi2 + 1))
            head = ' ' * (pos - lo2) + LAB[q] if lo2 <= pos <= hi2 else ''
            out.append((t, LAB[q], pos, row, head))
        try:
            nxt = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        tr = tab.get((q, h))
        if tr is None:
            break
        tape[pos] = tr[0]           # the symbol WRITTEN, not the one read
        pos += tr[1]                # then the move
        cfg = nxt
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec', required=True)
    ap.add_argument('--t0', type=int, default=0)
    ap.add_argument('--t1', type=int, default=200)
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--lo', type=int)
    ap.add_argument('--hi', type=int)
    ap.add_argument('--ruler', action='store_true')
    ap.add_argument('--mark', action='store_true',
                    help='show the state letter AT the head cell')
    ap.add_argument('--rests', action='store_true',
                    help='only rows whose head reads a BLANK')
    a = ap.parse_args()
    rows = run(a.spec, a.t0, a.t1, a.every, a.lo, a.hi, None, a.rests)
    if a.ruler and rows:
        lo = a.lo if a.lo is not None else 0
        n = len(rows[0][3])
        print('%-8s %-2s %-4s %s' % ('', '', 'col', ''.join(
            str((lo + i) % 10) for i in range(n))))
    lo0 = a.lo if a.lo is not None else 0
    for (t, q, pos, row, head) in rows:
        if a.mark and lo0 <= pos < lo0 + len(row):
            i = pos - lo0
            row = row[:i] + q.lower() + row[i + 1:]
        print('%-8d %s p=%-4d %s' % (t, q, pos, row))


if __name__ == '__main__':
    main()
