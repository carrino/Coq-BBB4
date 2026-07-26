#!/usr/bin/env python3
"""Differential lap decomposer for double_counter #32,
1RB1LD_1RC0RB_1LA0RC_0LD0LA.

Same contract as lap6.py: rebuild the whole lap out of ONLY the unit runs the
Coq file will use, and diff the composite against the raw stepper.  If this
prints ALL OK the decomposition is the one to transcribe.

MEASURED anchor (not the certificate's -- see the anchor trap in
docs/HOLDOUTS_WAVE14.md S4), exact for j = 1..6:

    Cf(j) = (StB, (rep [S0] z ++ rep [S1;S1;S0] k ++ [S1;S1;S1], S0, []))
            k = 2^j - 1,  z = 2j + 5

THREE engines, all walled on both sides, so all three are WTape combinators
(cycR / cycL) -- no new closer needed:

  RATCHET  cycR, P=5, q=StB, h=S1, u=[S0;S1;S0], w=[S1;S1;S0]
           (StB,([],S1,[S0;S1;S0])) -5-> (StB,([S1;S1;S0],S1,[]))
           crosses 010 rightward and lays 110 -- builds one comb unit

  COMB_L   cycL, P=3, q=StA, h=S1, u=[S0;S1;S1], rw=[], w=[S0;S0;S1]
           (StA,([S0;S1;S1],S1,[])) -3-> (StA,([],S1,[S0;S0;S1]))
           crosses one 011 comb unit leftward and lays 100 -- the return

  RETURN   cycL, P=2, q=StA, h=S1, u=[S1;S1], rw=[], w=[S0;S1]
           (StA,([S1;S1],S1,[])) -2-> (StA,([],S1,[S0;S1]))
           halves the ones -- the accumulator decrementing; fires exactly
           2^j times per lap (once per era)

Measured coverage by these three alone: 46.7 / 68.2 / 82.4 / 90.7 / 95.2 %
for j = 1..5, RISING with j.  That is the signature of a complete inventory:
what is left is a FIXED-SIZE boundary gadget per era (~57 steps), not a
growing one, so its share goes to 0.  Those residual runs are the handful of
[csteps] reflexivity lemmas the Coq file still needs; the script prints their
lengths so they can be read off one at a time.

Every unit application is checked against the raw stepper inside the loop
(the assert in decompose), and the composite is diffed against the raw lap
length, so "ALL OK" means the model is exact, not merely plausible.

Usage:  lap32.py [jmax]
"""
import sys
from collections import Counter

TM = {(0, 0): (1, +1, 1), (0, 1): (1, -1, 3),   # A0=1RB A1=1LD
      (1, 0): (1, +1, 2), (1, 1): (0, +1, 1),   # B0=1RC B1=0RB
      (2, 0): (1, -1, 0), (2, 1): (0, +1, 2),   # C0=1LA C1=0RC
      (3, 0): (0, -1, 3), (3, 1): (0, -1, 0)}   # D0=0LD D1=0LA
LAB = "ABCD"
StA, StB, StC, StD = 0, 1, 2, 3


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def cstep(c):
    st, (l, h, r) = c
    w, d, ns = TM[(st, h)]
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r)))
    return (ns, (ctl(l), chd(l), [w] + r))


def csteps(c, n):
    for _ in range(n):
        c = cstep(c)
    return c


def Cf(j):
    k, z = 2 ** j - 1, 2 * j + 5
    return (StB, ([0] * z + [1, 1, 0] * k + [1, 1, 1], 0, []))


# ----------------------------------------------------------------- the units
def unit_ratchet(c):
    """cycR: StB, h=S1, r starts [S0;S1;S0] -> 5 steps, +1 comb unit."""
    st, (l, h, r) = c
    if st == StB and h == 1 and r[:3] == [0, 1, 0]:
        return (StB, ([1, 1, 0] + l, 1, r[3:])), 5
    return None


def unit_comb_l(c):
    """cycL: StA, h=S1, l starts [S0;S1;S1] -> 3 steps.
    Crosses one 011 comb unit leftward and lays 100."""
    st, (l, h, r) = c
    if st == StA and h == 1 and l[:3] == [0, 1, 1]:
        return (StA, (l[3:], 1, [0, 0, 1] + r)), 3
    return None


def unit_return(c):
    """cycL: StA, h=S1, l starts [S1;S1] -> 2 steps, halve the ones."""
    st, (l, h, r) = c
    if st == StA and h == 1 and l[:2] == [1, 1]:
        return (StA, (l[2:], 1, [0, 1] + r)), 2
    return None


UNITS = [("ratchet", unit_ratchet), ("comb_l", unit_comb_l),
         ("return", unit_return)]


def decompose(j, verbose=False):
    """Run Cf(j) -> Cf(j+1) applying units greedily; single-step otherwise.

    Returns (steps, applied, boundary_runs) where boundary_runs counts the
    maximal single-step stretches -- the remaining unit inventory."""
    c, tgt = Cf(j), Cf(j + 1)
    n = 0
    applied = Counter()
    boundaries = Counter()
    run = 0
    guard = 0
    while c != tgt:
        guard += 1
        if guard > 5000000:
            return None, applied, boundaries
        hit = None
        for name, f in UNITS:
            got = f(c)
            if got:
                hit = (name,) + got
                break
        if hit:
            if run:
                boundaries[run] += 1
                run = 0
            name, c2, k = hit
            # the unit must agree with the raw stepper, or the model is wrong
            raw = csteps(c, k)
            assert raw == c2, ("UNIT MISMATCH %s at step %d\n  raw %s\n  unit %s"
                               % (name, n, raw, c2))
            c, n = c2, n + k
            applied[name] += 1
        else:
            c = cstep(c)
            n += 1
            run += 1
    if run:
        boundaries[run] += 1
    return n, applied, boundaries


def raw_lap(j, cap=5000000):
    c, tgt = Cf(j), Cf(j + 1)
    for n in range(1, cap):
        c = cstep(c)
        if c == tgt:
            return n
    return None


def main():
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    bad = 0
    for j in range(1, jmax + 1):
        nd, applied, bnd = decompose(j)
        nr = raw_lap(j)
        ok = nd is not None and nd == nr
        if not ok:
            bad += 1
        cov = 0 if nd is None else 100.0 * (nd - sum(k * v for k, v in bnd.items())) / nd
        print("j=%-2d k=%-4d z=%-3d  dec=%-8s raw=%-8s %s  units: %s  "
              "boundary runs: %s  unit-covered=%.1f%%"
              % (j, 2 ** j - 1, 2 * j + 5, nd, nr, "OK" if ok else "MISMATCH",
                 dict(applied), dict(sorted(bnd.items())), cov))
    print("laps: %s" % ("ALL OK" if not bad else "%d BAD" % bad))


if __name__ == '__main__':
    main()
