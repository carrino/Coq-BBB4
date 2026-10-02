#!/usr/bin/env python3
"""LE8 helper (UNTRUSTED): run from a hand-built configuration and print it
in absolute cells.  python3 ovlook.py SPEC Q SIDE PRE DIGITS... --steps N --states S
left side cells are given nearest-first; printed left to right."""
import sys
from csim import parse


def run(spec, q, L, h, R, steps, states, lo=-40, hi=8, every=False):
    tab = parse(spec)
    tape = {}
    for i, c in enumerate(L):
        tape[-1 - i] = c
    tape[0] = h
    for i, c in enumerate(R):
        tape[1 + i] = c
    pos = 0
    for t in range(steps):
        if 'ABCD'[q] in states:
            s = ''
            for k in range(lo, hi):
                s += ('[' + 'ABCD'[q] + ']' if k == pos else ' ') + str(tape.get(k, 0))
            print('%6d %s' % (t, s))
        e = tab[(q, tape.get(pos, 0))]
        w, d, nq = e
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq


if __name__ == '__main__':
    import json
    a = json.loads(sys.argv[1])
    run(a['spec'], 'ABCD'.index(a['q']), a['L'], a['h'], a['R'], a.get('steps', 300), a.get('states', 'ABCD'),
        a.get('lo', -40), a.get('hi', 8))
