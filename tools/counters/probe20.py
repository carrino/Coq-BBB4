#!/usr/bin/env python3
"""CTape-faithful mirror for tower #20 (1RB0RD_1LC1LB_1RA0LB_1LC1RA).

Same shape as probe15.py: the half-tapes are LISTS, blank beyond the end,
and [chd]/[ctl] are CTape's, so a window that holds here transcribes to Coq
unchanged.  UNTRUSTED, like everything under tools/.
"""
A, B, C, D = 0, 1, 2, 3
S0, S1 = 0, 1

# 1RB0RD_1LC1LB_1RA0LB_1LC1RA
TM = {(A, S0): (S1, 'R', B), (A, S1): (S0, 'R', D),
      (B, S0): (S1, 'L', C), (B, S1): (S1, 'L', B),
      (C, S0): (S1, 'R', A), (C, S1): (S0, 'L', B),
      (D, S0): (S1, 'L', C), (D, S1): (S1, 'R', A)}

NM = 'ABCD'


def chd(l):
    return l[0] if l else S0


def ctl(l):
    return l[1:] if l else []


def cstep(c, T=TM):
    q, (L, h, R) = c
    tr = T.get((q, h))
    if tr is None:
        return None
    w, d, nq = tr
    if d == 'R':
        return (nq, ([w] + L, chd(R), ctl(R)))
    return (nq, (ctl(L), chd(L), [w] + R))


def csteps(n, c, T=TM):
    for _ in range(n):
        c = cstep(c, T)
        if c is None:
            return None
    return c


c0 = (A, ([], S0, []))


def show(c):
    if c is None:
        return 'None'
    q, (L, h, R) = c
    s = lambda xs: ''.join(str(x) for x in xs)
    return '%s [%s] %s [%s]' % (NM[q], s(L[::-1]), h, s(R))
