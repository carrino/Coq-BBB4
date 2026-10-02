#!/usr/bin/env python3
"""LE7 (UNTRUSTED, eyeballing): the instructions fired between consecutive
visits of an anchor (state, symbol, side), with the visit strings.
    python3 fires.py SPEC STEPS Q S SIDE [maxlines]"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'le6'))
from conj_check import parse


def visits(spec, N, q0, s0, side):
    tab = parse(spec); tape = {}; p = 0; q = 0
    fired = set(); out = []
    for t in range(N):
        s = tape.get(p, 0)
        if q == q0 and s == s0:
            cells = [i for i, v in tape.items() if v]
            st = None
            if side == 'R' and (not cells or min(cells) >= p):
                st = ''.join(str(tape.get(i, 0)) for i in range(p + 1, max(cells + [p]) + 1))
            elif side == 'L' and (not cells or max(cells) <= p):
                st = ''.join(str(tape.get(i, 0)) for i in range(p - 1, min(cells + [p]) - 1, -1))
            if st is not None:
                out.append((t, st, ''.join(sorted(fired))))
                fired = set()
        v = tab[(q, s)]
        if v is None:
            break
        fired.add('ABCD'[q] + str(s))
        tape[p] = int(v[0]); p += 1 if v[1] == 'R' else -1; q = v[2]
    return out


if __name__ == '__main__':
    a = sys.argv[1:]
    mx = int(a[5]) if len(a) > 5 else 100
    for t, st, f in visits(a[0], int(a[1]), 'ABCD'.index(a[2]), int(a[3]), a[4])[:mx]:
        print('%9d %-12s %s' % (t, f, st))
