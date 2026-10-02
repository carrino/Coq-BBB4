#!/usr/bin/env python3
"""LE7 (eyeballing): the whole tape, head marked, at every step where the
head turns at either END of the visited span, in [t0, t1).
    python3 snap.py SPEC T0 T1 [maxlines] [every]"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'le6'))
from conj_check import parse


def run(spec, t0, t1, mx=200, every=1, mode='ends'):
    tab = parse(spec); tape = {}; p = 0; q = 0; lo = hi = 0; n = 0
    for t in range(t1):
        s = tape.get(p, 0)
        v = tab[(q, s)]
        if v is None:
            break
        mv = 1 if v[1] == 'R' else -1
        hit = (p == lo and mv == 1) or (p == hi and mv == -1) if mode == 'ends' else (('ABCD'[q] + str(s)) == mode)
        if t >= t0 and hit:
            n += 1
            if n % every == 0:
                print('%9d %s' % (t, ''.join(('ABCD'[q] if x == p else '') + str(tape.get(x, 0))
                                             for x in range(lo, hi + 1))))
                mx -= 1
                if mx <= 0:
                    return
        tape[p] = int(v[0]); p += mv; q = v[2]
        lo = min(lo, p); hi = max(hi, p)


if __name__ == '__main__':
    a = sys.argv[1:]
    run(a[0], int(a[1]), int(a[2]), int(a[3]) if len(a) > 3 else 200,
        int(a[4]) if len(a) > 4 else 1, a[5] if len(a) > 5 else 'ends')
