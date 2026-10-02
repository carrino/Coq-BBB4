#!/usr/bin/env python3
"""LE8 helper (UNTRUSTED): from a hand-built start, list every visit to an
anchor shape (state q reading h) with its near and far cells.
python3 anch.py JSON   (spec, q, L (nearest-first), h, R, steps, aq, ah, side, nfar)"""
import json, sys
from csim import parse


def main():
    a = json.loads(sys.argv[1])
    tab = parse(a['spec'])
    tape = {}
    for i, c in enumerate(a['L']):
        tape[-1 - i] = c
    tape[0] = a['h']
    for i, c in enumerate(a['R']):
        tape[1 + i] = c
    pos, q = 0, 'ABCD'.index(a['q'])
    aq, ah = 'ABCD'.index(a['aq']), a['ah']
    lo = min(tape) - 2
    hi = max(tape) + 2
    for t in range(a['steps']):
        lo = min(lo, pos - 1); hi = max(hi, pos + 1)
        if q == aq and tape.get(pos, 0) == ah:
            left = ''.join(str(tape.get(j, 0)) for j in range(pos - 1, lo - 1, -1)).rstrip('0')
            right = ''.join(str(tape.get(j, 0)) for j in range(pos + 1, hi + 1)).rstrip('0')
            if a.get('side', 'L') == 'L':
                print('%6d off %4d  far(R) %-12s near(L) %s' % (t, pos, right, left))
            else:
                print('%6d off %4d  far(L) %-12s near(R) %s' % (t, pos, left, right))
        w, d, nq = tab[(q, tape.get(pos, 0))]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq


if __name__ == '__main__':
    main()
