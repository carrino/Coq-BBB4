#!/usr/bin/env python3
"""Differential lap decomposer for the two 1RB--- wrap holdouts (UNTRUSTED).

    W15  = 1RB---_1RC0RB_0LC0RD_1LD1LB
    W07  = 1RB---_1LC0LB_0RC0LD_1RD1RB
    W07m = mirror(W07) = 1LB---_1RC0RB_0LC0RD_1LD1LB

W07m and W15 differ ONLY in A0's direction, so they share the {B,C,D}
core table verbatim -- and both boot to the SAME anchor:

    E(n) = (StB, ([], S0, rep [S1] n))      "B on blank, 1^n to the right"

    W15  reaches E(3) in 7 steps,   W07m reaches E(3) in 6 steps.

so ONE set of lap lemmas over a core-only Coq section boards both, W07 by
Mirror.mirror_iqh.  That is the whole reason this file models the core rather
than either machine.

MEASURED lap (exact, blank-tape run, j = 1..8):  E(n) -> E(2n+1),
n = 3, 7, 15, 31, 63, 127, 255, 511 at steps 7, 32, 121, 434, 1579, 5924,
22813, 89366 -- lap length n^2 + 6n - 2.

Same contract as lap6.py/lap32.py: rebuild the whole lap out of ONLY the unit
runs the Coq file will use, and diff the composite against the raw stepper.
Unlike those two this decomposition is COMPLETE -- no boundary-gadget
residue -- so "ALL OK" means unit-covered = 100%, and any single-step
stretch is a modelling bug, not leftover work.

The seven units (all frame-polymorphic; L and r never destructured beyond
what is written):

  RATCHET  (StB, (L, S0, S1::S1::r))    -3-> (StB, (S1::L, S0, S1::r))
  TURN1    (StB, (S1::L, S0, [S1]))     -5-> (StB, (L, S1, [S1;S1;S1]))
  SWEEPR   (StB, (L, S1, r))            -1-> (StB, (S0::L, chd r, ctl r))
  TURN2    (StB, (L, S0, []))           -3-> (StD, (S0::L, S0, []))
  SWEEPL   (StD, (S0::L, S0, r))        -1-> (StD, (L, S0, S1::r))
  TURNL    (StD, (S1::S1::L, S0, r))    -2-> (StB, (L, S1, S1::S1::r))
  TURNL1   (StD, ([S1], S0, r))         -2-> (StB, ([], S0, S1::S1::r))

and the lap they compose to, for n = 2m+3:

  E(n)  --RATCHET x (n-1)-->  (StB, (1^(n-1), S0, [S1]))
        --TURN1-->            (StB, (1^(n-2), S1, 1^3))
        --BOUNCE x m-->       (StB, ([S1],    S1, 1^(4m+3)))
        --CLOSE-->            E(2n+1)

  BOUNCE = SWEEPR^(b+1) . TURN2 . SWEEPL^(b+2) . TURNL     (a -= 2, b += 4)
  CLOSE  = SWEEPR^(b+1) . TURN2 . SWEEPL^(b+2) . TURNL1    (a = 1 -> E(b+4))

Usage:  lapwrap.py [jmax]
"""
import sys
from collections import Counter

LAB = "ABCD"
StA, StB, StC, StD = 0, 1, 2, 3
S0, S1 = 0, 1

SPECS = {
    'W15': "1RB---_1RC0RB_0LC0RD_1LD1LB",
    'W07': "1RB---_1LC0LB_0RC0LD_1RD1RB",
    'W07m': "1LB---_1RC0RB_0LC0RD_1LD1LB",
}


def parse(spec):
    tm = {}
    for q, blk in enumerate(spec.split('_')):
        for s in (0, 1):
            t = blk[3 * s:3 * s + 3]
            tm[(q, s)] = None if t == '---' else (
                int(t[0]), +1 if t[1] == 'R' else -1, LAB.index(t[2]))
    return tm


CORE = parse(SPECS['W15'])


def chd(l):
    return l[0] if l else S0


def ctl(l):
    return l[1:] if l else []


def cstep(c, tm=CORE):
    st, (l, h, r) = c
    t = tm[(st, h)]
    if t is None:
        return None
    w, d, ns = t
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r)))
    return (ns, (ctl(l), chd(l), [w] + r))


def csteps(c, n, tm=CORE):
    for _ in range(n):
        c = cstep(c, tm)
        if c is None:
            return None
    return c


def E(n):
    return (StB, ([], S0, [S1] * n))


# ----------------------------------------------------------------- the units
def u_ratchet(c):
    st, (l, h, r) = c
    if st == StB and h == S0 and r[:2] == [S1, S1]:
        return (StB, ([S1] + l, S0, r[1:])), 3
    return None


def u_turn1(c):
    st, (l, h, r) = c
    if st == StB and h == S0 and r == [S1] and l[:1] == [S1]:
        return (StB, (l[1:], S1, [S1, S1, S1])), 5
    return None


def u_sweepr(c):
    st, (l, h, r) = c
    if st == StB and h == S1:
        return (StB, ([S0] + l, chd(r), ctl(r))), 1
    return None


def u_turn2(c):
    st, (l, h, r) = c
    if st == StB and h == S0 and r == []:
        return (StD, ([S0] + l, S0, [])), 3
    return None


def u_sweepl(c):
    st, (l, h, r) = c
    if st == StD and h == S0 and l[:1] == [S0]:
        return (StD, (l[1:], S0, [S1] + r)), 1
    return None


def u_turnl(c):
    st, (l, h, r) = c
    if st == StD and h == S0 and l[:2] == [S1, S1]:
        return (StB, (l[2:], S1, [S1, S1] + r)), 2
    return None


def u_turnl1(c):
    st, (l, h, r) = c
    if st == StD and h == S0 and l == [S1]:
        return (StB, ([], S0, [S1, S1] + r)), 2
    return None


# TURNL1 must be tried before TURNL only if both could match; they cannot
# (l == [S1] vs l starts [S1;S1]), so any order is fine.  RATCHET before
# SWEEPR matters: at h = S0 they are disjoint anyway (SWEEPR needs h = S1).
UNITS = [("ratchet", u_ratchet), ("turn1", u_turn1), ("sweepr", u_sweepr),
         ("turn2", u_turn2), ("sweepl", u_sweepl), ("turnl1", u_turnl1),
         ("turnl", u_turnl)]


def decompose(n, cap=20000000):
    """E(n) -> E(2n+1) applying units greedily; single-step otherwise."""
    c, tgt = E(n), E(2 * n + 1)
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


def raw_lap(n, cap=20000000):
    c, tgt = E(n), E(2 * n + 1)
    for k in range(1, cap):
        c = cstep(c)
        if c == tgt:
            return k
    return None


def boots():
    """Where does each real machine first hit E(3)?"""
    out = {}
    for name in ('W15', 'W07m'):
        tm = parse(SPECS[name])
        c, t = (StA, ([], S0, [])), 0
        while t < 200 and c != E(3):
            c = cstep(c, tm)
            t += 1
        out[name] = t if c == E(3) else None
    return out


def main():
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    print("boot to E(3):  %s" % boots())
    bad = 0
    n = 3
    for _ in range(jmax):
        nd, applied, bnd = decompose(n)
        nr = raw_lap(n)
        pred = n * n + 6 * n - 2
        ok = nd is not None and nd == nr == pred and not bnd
        if not ok:
            bad += 1
        m = (n - 3) // 2
        exp = {"ratchet": n - 1, "turn1": 1, "turn2": m + 1,
               "sweepr": sum(2 * (3 + 4 * i) + 1 for i in range(m + 1)) // 1,
               "turnl": m, "turnl1": 1}
        # sweepr/sweepl counts, closed form: b_i = 3+4i for i = 0..m
        exp["sweepr"] = sum((3 + 4 * i) + 1 for i in range(m + 1))
        exp["sweepl"] = sum((3 + 4 * i) + 2 for i in range(m + 1))
        match = all(applied[k] == v for k, v in exp.items())
        print("n=%-5d dec=%-10s raw=%-10s n^2+6n-2=%-10s %s  units=%s%s"
              % (n, nd, nr, pred, "OK" if ok else "MISMATCH", dict(applied),
                 "" if match else "  UNIT-COUNT MISMATCH exp=%s" % exp))
        if bnd:
            print("    UNMODELLED single-step runs: %s" % dict(sorted(bnd.items())))
        if not match:
            bad += 1
        n = 2 * n + 1
    print("laps: %s" % ("ALL OK" if not bad else "%d BAD" % bad))


if __name__ == '__main__':
    main()
