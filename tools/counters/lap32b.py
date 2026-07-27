#!/usr/bin/env python3
"""Differential lap decomposer for #32 at BBB's anchor (UNTRUSTED).

    1RB1LD_1RC0RB_1LA0RC_0LD0LA

SUPERSEDES lap32.py.  That file anchored on the head-on-blank config with
comb count k = 2^j - 1 and comb unit (011); it validated, but topped out at
95.2% unit coverage with a fixed ~57-step boundary gadget per era.  BBB's
cert (results/counter32.cert, SUMMARY.md:2134) uses the head-on-rightmost-1
event with comb count a = 2^j and unit (110) -- the SAME orbit, phased one
cell over on the comb, but with a PURE doubling a -> 2a instead of
a -> 2a+1, which is what makes the phases line up.

MEASURED anchor (blank-tape run, exact for j = 0..3 at steps 33/101/311/1021):

    Cf(j) = (StB, (rep [S0] z ++ rep [S0;S1;S1] a ++ [S1], S1, []))
            a = 2^j,  z = 2j+3          (cconf left is NEAREST-FIRST, so
                                         [S0;S1;S1] reads 110 on the tape)

Candidate units, read off the j=1 lap (210 steps):

  COLLAPSE  cycL P=3  (StA, ([S0;S1;S1]++L, S1, r)) -> (StA, (L, S1, [S0;S0;S1]++r))
            crosses one 110 comb unit leftward, lays 100
  SPREAD    cycR P=5  (StB, (L, S0, [S1;S0;S0]++r)) -> (StB, ([S0;S1;S1]++L, S0, r))
            crosses one 100 rightward, lays 110 back -- the inverse crossing
  ZSWEEPL   P=1       (StD, ([S0]++L, S0, r))       -> (StD, (L, S0, [S0]++r))
            D0=0LD walking left over the 0-spacer
  ZSWEEPR   P=1       (StB, (L, S1, [S1]++r))       -> (StB, ([S0]++L, S1, r))
            B1=0RB zeroing the trailing 1-run at the end of the lap

Same contract as lap6.py/lap32.py: every unit application is re-checked
against the raw stepper inside the loop, and the composite is diffed against
the raw lap length.  What this script is FOR is the residual report: the
maximal single-step stretches it prints are exactly the boundary lemmas the
Coq file still needs, and whether their sizes stay FIXED as j grows is the
test of whether the engine inventory is complete.

Usage:  lap32b.py [jmax]
"""
import sys
from collections import Counter

LAB = "ABCD"
StA, StB, StC, StD = 0, 1, 2, 3
S0, S1 = 0, 1

TM = {(0, 0): (1, +1, 1), (0, 1): (1, -1, 3),   # A0=1RB A1=1LD
      (1, 0): (1, +1, 2), (1, 1): (0, +1, 1),   # B0=1RC B1=0RB
      (2, 0): (1, -1, 0), (2, 1): (0, +1, 2),   # C0=1LA C1=0RC
      (3, 0): (0, -1, 3), (3, 1): (0, -1, 0)}   # D0=0LD D1=0LA


def chd(l):
    return l[0] if l else S0


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
    a, z = 2 ** j, 2 * j + 3
    return (StB, ([S0] * z + [S0, S1, S1] * a + [S1], S1, []))


# ----------------------------------------------------------------- the units
def u_collapse(c):
    st, (l, h, r) = c
    if st == StA and h == S1 and l[:3] == [S0, S1, S1]:
        return (StA, (l[3:], S1, [S0, S0, S1] + r)), 3
    return None


def u_spread(c):
    st, (l, h, r) = c
    if st == StB and h == S0 and r[:3] == [S1, S0, S0]:
        return (StB, ([S0, S1, S1] + l, S0, r[3:])), 5
    return None


def u_zsweepl(c):
    st, (l, h, r) = c
    if st == StD and h == S0 and l[:1] == [S0]:
        return (StD, (l[1:], S0, [S0] + r)), 1
    return None


def u_zsweepr(c):
    st, (l, h, r) = c
    if st == StB and h == S1 and r[:1] == [S1]:
        return (StB, ([S0] + l, S1, r[1:])), 1
    return None


UNITS = [("collapse", u_collapse), ("spread", u_spread),
         ("zsweepl", u_zsweepl), ("zsweepr", u_zsweepr)]


def decompose(j, cap=40000000):
    c, tgt = Cf(j), Cf(j + 1)
    steps = 0
    applied = Counter()
    boundaries = Counter()
    run = 0
    while c != tgt:
        if steps > cap:
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
            raw = csteps(c, k)
            assert raw == c2, ("UNIT MISMATCH %s at step %d\n  raw  %s\n  unit %s"
                               % (name, steps, raw, c2))
            c, steps = c2, steps + k
            applied[name] += 1
        else:
            c = cstep(c)
            steps += 1
            run += 1
    if run:
        boundaries[run] += 1
    return steps, applied, boundaries


def raw_lap(j, cap=40000000):
    c, tgt = Cf(j), Cf(j + 1)
    for k in range(1, cap):
        c = cstep(c)
        if c == tgt:
            return k
    return None


def main():
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    bad = 0
    for j in range(0, jmax + 1):
        nd, applied, bnd = decompose(j)
        nr = raw_lap(j)
        ok = nd is not None and nd == nr
        if not ok:
            bad += 1
        unmodelled = sum(k * v for k, v in bnd.items())
        cov = 0.0 if not nd else 100.0 * (nd - unmodelled) / nd
        print("j=%-2d a=%-5d z=%-4d dec=%-8s raw=%-8s %s  units=%s"
              % (j, 2 ** j, 2 * j + 3, nd, nr, "OK" if ok else "MISMATCH",
                 dict(applied)))
        print("        boundary runs: %-40s unit-covered=%.1f%%  (%d steps)"
              % (dict(sorted(bnd.items())), cov, unmodelled))
    print("laps: %s" % ("ALL OK" if not bad else "%d BAD" % bad))


if __name__ == '__main__':
    main()
