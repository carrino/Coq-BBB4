#!/usr/bin/env python3
"""LE8 helper (UNTRUSTED): print a row's configurations in absolute cells.

    python3 look.py SPEC T0 T1 [STATES] [LO HI]
prints every step in [T0, T1) whose state is in STATES (default all)."""
import sys
from csim import parse, step


def main():
    spec, t0, t1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    sts = sys.argv[4] if len(sys.argv) > 4 else 'ABCD'
    lo = int(sys.argv[5]) if len(sys.argv) > 5 else -6
    hi = int(sys.argv[6]) if len(sys.argv) > 6 else 30
    tab = parse(spec)
    tape, pos, q = {}, 0, 0
    for t in range(t1):
        if t >= t0 and 'ABCD'[q] in sts:
            s = ''
            for k in range(lo, hi):
                s += ('[' + 'ABCD'[q] + ']' if k == pos else ' ') + str(tape.get(k, 0))
            print('%7d %s' % (t, s))
        w, d, nq = tab[(q, tape.get(pos, 0))]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq


if __name__ == '__main__':
    main()
