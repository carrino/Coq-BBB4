#!/usr/bin/env python3
"""The MIDDLE of tower #20's long lap: the ride window, the turn window, and
the five new joints they are built from -- each checked EXHAUSTIVELY, in the
exact form the Coq lemma will take, before any Coq is written.

WHAT THE MIDDLE IS.  After [lapB_pre] the configuration is

    (StC, (lay r E, S0, S1 :: wruns w))        wruns [n1;n2;..] = 1^n1 0 1^n2 0 ..

and the head sweeps RIGHT.  It enters each run on a 1, so the run it actually
READS at [n_i] is [n_i + 1]:

    n_i EVEN -> the run read is odd  -> the sweep RIDES over it and continues;
    n_i ODD  -> the run read is even -> that is the TURNAROUND.

THE RIDE, in closed form (this file's [ride_window]).  For [n = 2k]:

    (StC, (M, S0, S1 :: wruns (n :: t)))
      -(n+3)->  (StC, (alt k M, S0, S1 :: wruns t))       alt k M = (1 0)^k 1 M

so the cost is [n+3] and the debris is the ALTERNATING word of length [2k+1].
[out5] is the [k = 1] case and [k = 0] is a bare three-step window.

THE TURN (this file's [turn_window]).  For [n = 2k+1] the head crosses the
run, [A0 = 1RB] bounces it into [StB], and the [StB] walk-back is FOUR steps
([B1;B1;B1;B0]) when the next run is nonempty and ONE step ([B0]) when it is
not.  The four-step case lands on

    (StC, (arep k M, S1, wruns ((n2 + 3) :: t2)))        arep k M = (0 1)^k M

-- the [n2 + 3] of the abstract successor is exactly the four 1s the walk-back
lays, minus the one it consumed -- and [arep k M] is [RevP]-shaped debris
([a^k] in the block alphabet), which is what [lapB_post] already takes.  The
one-step case lands on [(StC, (alt k M, S1, S1 :: X))], whose debris is
[b a^k].

THE FIVE JOINTS.  [ad2] and the two walk-backs READ the context (they are
[chd]/[ctl] windows, trap 2), so "uniform over all contexts" is the wrong
test for them; every gadget here is instead checked by evaluating its EXACT
symbolic right-hand side against the raw simulator, over every [(L,R)] with
[|L|,|R| <= 4] -- 961 contexts each.  That is strictly stronger than
[lap20.py]'s [exhaustive] and it is what transcribes to Coq unchanged.

UNTRUSTED, like everything under tools/.  Usage: `python3 mid20.py`.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe20 import csteps, cstep, S0, S1  # noqa: E402

A, B, C, D = 0, 1, 2, 3


def chd(l):
    return l[0] if l else S0


def ctl(l):
    return l[1:] if l else []


def ctxs(maxlen=4):
    """Every (L, R) with |L|, |R| <= maxlen -- 961 pairs at maxlen = 4."""
    ws = [list(x) for k in range(maxlen + 1)
          for x in itertools.product([S0, S1], repeat=k)]
    for L in ws:
        for R in ws:
            yield L, R


# ---------------------------------------------------------------- joints
# Each entry: name, cost, lhs(L,R) -> config, rhs(L,R) -> config.
JOINTS = [
    # the two-step A/D stride: eats two 1s, lays [1;0].  chd/ctl on the RIGHT.
    ('ad2', 2,
     lambda L, R: (A, (L, S1, [S1] + R)),
     lambda L, R: (A, ([S1, S0] + L, chd(R), ctl(R)))),

    # the ride's last two steps: A over the run terminator, D back into C.
    ('fin2', 2,
     lambda L, R: (A, (L, S1, [S0] + R)),
     lambda L, R: (C, (L, S0, [S1] + R))),

    # the turn's three steps: A1, D1, then A0 = 1RB bounces into StB.
    ('turn3', 3,
     lambda L, R: (A, (L, S1, [S1, S0] + R)),
     lambda L, R: (B, ([S1, S1, S0] + L, chd(R), ctl(R)))),

    # the StB walk-back, next run NONEMPTY: B1,B1,B1,B0.  chd/ctl on the LEFT.
    ('wb4', 4,
     lambda L, R: (B, ([S1, S1, S0] + L, S1, R)),
     lambda L, R: (C, (ctl(L), chd(L), [S1, S1, S1, S1] + R))),

    # the StB walk-back, next run EMPTY: B0 at once.
    ('wb1', 1,
     lambda L, R: (B, ([S1, S1, S0] + L, S0, R)),
     lambda L, R: (C, ([S1, S0] + L, S1, [S1] + R))),
]


def check_joints():
    bad = []
    for nm, n, lhs, rhs in JOINTS:
        for L, R in ctxs():
            got = csteps(n, lhs(L, R))
            want = rhs(L, R)
            if got != want:
                bad.append('%s: L=%s R=%s got %s want %s' % (nm, L, R, got, want))
                break
    print('#20 five new joints, each over all 961 (L,R) with |L|,|R| <= 4: %s'
          % ('OK' if not bad else bad[0]))
    return bad


# ------------------------------------------------------------- the windows
def alt(k, M):
    """(1 0)^k 1 M -- the ride's debris, length 2k+1 over M."""
    return [S1, S0] * k + [S1] + M


def arep(k, M):
    """(0 1)^k M -- the turn's debris; RevP-shaped, [a^k] in blocks."""
    return [S0, S1] * k + M


def wruns(w):
    out = []
    for n in w:
        out += [S1] * n + [S0]
    return out


def check_ride(kmax=7):
    """(StC,(M,S0,S1::wruns(2k::t))) -(2k+3)-> (StC,(alt k M,S0,S1::wruns t))"""
    bad = []
    for k in range(kmax + 1):
        for M, X in ctxs(3):
            lhs = (C, (M, S0, [S1] + [S1] * (2 * k) + [S0] + X))
            got = csteps(2 * k + 3, lhs)
            want = (C, (alt(k, M), S0, [S1] + X))
            if got != want:
                bad.append('k=%d M=%s X=%s got %s want %s' % (k, M, X, got, want))
                break
    print('#20 ride window, k <= %d over all (M,X) with |M|,|X| <= 3: %s'
          % (kmax, 'OK' if not bad else bad[0]))
    return bad


def check_turn(kmax=7):
    """n = 2k+1.  The bounce into StB is at 2k+4; then the walk-back is FOUR
    steps if the next cell is a 1 and ONE step if it is not."""
    bad = []
    for k in range(kmax + 1):
        for M, X in ctxs(3):
            lhs = (C, (M, S0, [S1] + [S1] * (2 * k + 1) + [S0] + X))
            if chd(X) == S1:
                cost = (2 * k + 4) + 4
                want = (C, (arep(k, M), S1, [S1] * 4 + ctl(X)))
            else:
                cost = (2 * k + 4) + 1
                want = (C, (alt(k + 1, M), S1, [S1] + ctl(X)))
            got = csteps(cost, lhs)
            if got != want:
                bad.append('k=%d M=%s X=%s got %s want %s' % (k, M, X, got, want))
                break
    print('#20 turn window, k <= %d over all (M,X) with |M|,|X| <= 3: %s'
          % (kmax, 'OK' if not bad else bad[0]))
    return bad


def turn_cost(k, t):
    """Cost of the turn at n = 2k+1 with the run-length tail [t]."""
    return (2 * k + 4) + (4 if (t and t[0] != 0) else 1)


def turn_after(k, t, M):
    """Where the turn lands, on the run-length word."""
    if t and t[0] != 0:
        return (C, (arep(k, M), S1, wruns([t[0] + 3] + t[1:])))
    return (C, (alt(k + 1, M), S1, [S1] + (wruns(t[1:]) if t else [])))


def check_turn_word(kmax=5):
    """The turn read on the RUN-LENGTH word: the next entry becomes n2+3,
    and the debris is [a^k] (resp. [b a^k] with nothing beyond)."""
    bad = []
    for k in range(kmax + 1):
        n = 2 * k + 1
        for t in ([], [0], [1], [2], [5], [0, 2], [3, 1], [2, 2, 1], [4, 0, 3]):
            M = [S1, S0, S1]
            got = csteps(turn_cost(k, t), (C, (M, S0, [S1] + wruns([n] + t))))
            want = turn_after(k, t, M)
            if got != want:
                bad.append('k=%d t=%s got %s want %s' % (k, t, got, want))
    print('#20 turn on the run-length word (the n2+3), k <= %d: %s'
          % (kmax, 'OK' if not bad else bad[0]))
    return bad


def ride_debris(evens, M):
    """The left list after riding over the even prefix, innermost last."""
    out = M
    for n in evens:
        out = alt(n // 2, out)
    return out


def check_middle(cases=None):
    """The whole middle: ride over the even prefix, then turn.  Diffed against
    the raw simulator for the cost AND the configuration."""
    cases = cases or [[1, 4], [7], [2, 7], [4, 1, 2, 1], [1, 2, 5, 1],
                      [5, 5, 1], [1, 1, 8, 1], [4, 8, 1], [2, 2, 1, 1, 1, 2, 1],
                      [8, 2, 3, 1], [0, 1, 4], [6, 6, 3], [2, 4, 8, 5, 2, 1]]
    bad = []
    for w in cases:
        i = next((j for j, x in enumerate(w) if x % 2), None)
        if i is None:
            continue
        M = [S1, S0, S1, S0, S1, S1]
        k, t = (w[i] - 1) // 2, w[i + 1:]
        cost = sum(n + 3 for n in w[:i]) + turn_cost(k, t)
        got = csteps(cost, (C, (M, S0, [S1] + wruns(w))))
        want = turn_after(k, t, ride_debris(w[:i], M))
        if got != want:
            bad.append('w=%s cost=%d\n     got  %s\n     want %s'
                       % (w, cost, got, want))
    print('#20 middle (ride^* then turn) against the simulator, %d words: %s'
          % (len(cases), 'OK' if not bad else bad[0]))
    return bad


def main():
    bad = []
    bad += check_joints()
    bad += check_ride()
    bad += check_turn()
    bad += check_turn_word()
    bad += check_middle()
    print('#20 middle: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
