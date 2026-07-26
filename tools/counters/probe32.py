#!/usr/bin/env python3
"""Recon probe for double_counter #32, 1RB1LD_1RC0RB_1LA0RC_0LD0LA.

MEASURED anchor (NOT the certificate's -- see the anchor trap in
docs/HOLDOUTS_WAVE14.md S4: verify.c's build and the reachable orbit differ,
and only the reachable one closes in Coq).  Read straight off the blank-tape
run, exact for j = 1..6:

    Cf(j) = (StB, (rep [S0] z ++ rep [S1;S1;S0] k ++ [S1;S1;S1], S0, []))
            k = 2^j - 1,  z = 2j + 5

i.e. tape order  1^3 (011)^k 0^z  with the head on the blank past the last 0.
Lap lengths 210, 710, 2574, 9758, 37950 -- ratio -> 4, so Theta(len^2).

Sweep decomposition of one lap (maximal same-direction runs):

    B+1:1  A-1:LONG | B+1:3 A-1:1 (B+1:4 A-1:1)^k B+1:3 | A-1:LONG | ...

The inner repeat count is EXACTLY k, so it is a cycR unit (5 steps, net +3).
The bracketing B+1:3 / B+1:3 are the entry and exit gadgets.  Later groups in
the same lap show B+1:5 in place of a B+1:4 -- that is the 0^z accumulator's
CARRY firing, i.e. this is the same two-level shape as #30: a comb ratchet
inside an odometer, not a flat translated cycle.

So #32 is in #30's difficulty class, not #6's.  Before writing Coq, extend
this into a full lap*.py in the lap6.py mould -- pin every unit as a
standalone fact, rebuild the lap from ONLY those units, diff against the raw
stepper over j = 1..7 -- and in particular read the accumulator's carry rule
off the executor rather than deriving it (the same warning the #30 recon
carries; its digit transitions change LENGTH).

Usage:  probe32.py [jmax]        verify the anchor + print sweep structure
"""
import sys

TM = {(0, 0): (1, +1, 1), (0, 1): (1, -1, 3),   # A0=1RB A1=1LD
      (1, 0): (1, +1, 2), (1, 1): (0, +1, 1),   # B0=1RC B1=0RB
      (2, 0): (1, -1, 0), (2, 1): (0, +1, 2),   # C0=1LA C1=0RC
      (3, 0): (0, -1, 3), (3, 1): (0, -1, 0)}   # D0=0LD D1=0LA
LAB = "ABCD"


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def cstep(c):
    st, (l, h, r) = c
    w, d, ns = TM[(st, h)]
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r))), +1
    return (ns, (ctl(l), chd(l), [w] + r)), -1


def Cf(j):
    """The MEASURED event anchor; k = 2^j - 1 comb units, z = 2j + 5 gap."""
    k, z = 2 ** j - 1, 2 * j + 5
    return (1, ([0] * z + [1, 1, 0] * k + [1, 1, 1], 0, []))


def lap(j, cap=4000000):
    """Run Cf(j) -> Cf(j+1); return (steps, sweeps) or (None, None)."""
    c, tgt = Cf(j), Cf(j + 1)
    n, lastd, seglen, segs, st0 = 0, 0, 0, [], c[0]
    while n < cap:
        c, d = cstep(c)
        n += 1
        if d != lastd and lastd != 0:
            segs.append((LAB[st0], lastd, seglen))
            st0, seglen = c[0], 1
        else:
            seglen += 1
        lastd = d
        if c == tgt:
            segs.append((LAB[st0], lastd, seglen))
            return n, segs
    return None, None


def main():
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    prev = None
    for j in range(1, jmax + 1):
        n, segs = lap(j)
        if n is None:
            print("j=%d  ANCHOR MISS" % j)
            continue
        ratio = n / prev if prev else 0.0
        prev = n
        print("j=%-2d k=%-4d z=%-3d  lap=%-7d ratio=%.2f  sweeps=%d"
              % (j, 2 ** j - 1, 2 * j + 5, n, ratio, len(segs)))
        if j <= 3:
            print("     " + ' '.join("%s%+d:%d" % s for s in segs[:24])
                  + (" ..." if len(segs) > 24 else ""))


if __name__ == '__main__':
    main()
