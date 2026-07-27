#!/usr/bin/env python3
"""The nine step-gadgets of 1RB1LD_1RC0RB_1LA0RC_0LD0LA (double #32), each a
CTape-faithful `csteps` identity uniform in the surrounding tape.  Every one
is a one-line `reflexivity` in Coq; this file is the differential check.

See docs/HOLDOUTS_MXDYS_SN.md section 5b for how they assemble into R1/R2/R3.
UNTRUSTED, like everything under tools/.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe32b import cstep, chd, ctl, A, B, C, D, S0, S1

def T(n, c):
    for _ in range(n):
        c = cstep(c)
        if c is None:
            return None
    return c

Ls = [[], [S1], [S0, S1], [S1, S0, S1, S1], [S0, S1, S1, S0, S1, S1, S1]]
Rs = [[], [S1], [S0, S0, S1], [S1, S1], [S0, S1, S0, S0, S1, S1]]

def main():
    bad = 0
    def chk(nm, got, want, x=''):
        nonlocal bad
        if got != want:
            bad += 1
            print('  FAIL %-4s %s\n    got  %s\n    want %s' % (nm, x, got, want))
    for L in Ls:
        for R in Rs:
            # -- rightward
            chk('bt4', T(4, (A, (L, S0, [S0, S1, S0] + R))),
                (A, ([S1, S1] + L, S0, [S1] + R)), (L, R))
            chk('rc5', T(5, (A, (L, S0, [S1, S0, S1, S0] + R))),
                (A, ([S1, S0, S1] + L, S0, [S1] + R)), (L, R))
            # -- turnarounds
            chk('tn4', T(4, (A, (L, S0, [S1, S0, S0] + R))),
                (A, ([S0, S1] + L, S1, [S1] + R)), (L, R))
            chk('tn6', T(6, (A, (L, S0, [S1, S0, S1, S1, S0, S0] + R))),
                (A, ([S0, S1, S0, S1] + L, S0, [S1, S0] + R)), (L, R))
            chk('md3', T(3, (A, (L, S0, [S0, S0, S1] + R))),
                (A, ([S1] + L, S1, [S1, S1] + R)), (L, R))
            # -- leftward
            for M in Ls:
                chk('lc3', T(3, (A, ([S0, S1] + M, S1, R))),
                    (A, (ctl(M), chd(M), [S0, S0, S1] + R)), (M, R))
                chk('la2', T(2, (A, ([S1] + M, S1, R))),
                    (A, (ctl(M), chd(M), [S0, S1] + R)), (M, R))
            # -- the two run sweeps used by R1
            chk('b1', T(1, (B, (L, S1, R))), (B, ([S0] + L, chd(R), ctl(R))), (L, R))
            chk('d0', T(1, (D, (L, S0, R))), (D, (ctl(L), chd(L), [S0] + R)), (L, R))
    print('all nine #32 gadgets: %s' % ('OK' if bad == 0 else '%d FAILURES' % bad))
    return 1 if bad else 0

if __name__ == '__main__':
    sys.exit(main())
