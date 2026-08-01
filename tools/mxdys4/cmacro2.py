#!/usr/bin/env python3
"""UNTRUSTED: the macro system of

    1RB0RB_0LC1RD_1LC1LA_0LA1RB          ("the phi row")

in CCONF coordinates -- the form a Coq proof would be written in --
differentially validated against the raw simulator.

This row passes the wave-36 lever test: its orbit keeps the RIGHT half-tape
a bare unary run for its whole life (0 violations in 2,000,000 steps,
`tools/mxdys4/extract.py SPEC R1`), so the configuration collapses to

    (StA, (l, s, rep [S1] R ++ S0 :: Z))

with

  l  the left half-tape, NEAREST CELL FIRST (so l[0] is the cell the head
     would step onto going left, and `chd []` = S0 = the blank),
  s  the head symbol,
  R  the length of the unary run to the right of the head,
  Z  a tail no rule touches.

As on M1/M4 the shape must carry the EXPLICIT BLANK and then the generic
tail: rules 3-6 walk one cell past the run and must find a blank there, and
they consume it and write a fresh one, so without `Z` underneath the output
of one rule does not syntactically match the input of the next.

SIX rules, exhaustive over (s, R) with the R>=1 rules split by parity:

  (1) s=S0, R=0              -> (ctl l, chd l, 1)                    3
  (2) s=S1, R=0, l=0^j 1 l1  -> (ctl l1, chd l1, j+2)                j+4
  (3) s=S0, R=2k+1           -> (1^(2k+1) ++ l, S1, 0)               2k+3
  (4) s=S0, R=2k+2           -> (1^(2k+1) ++ l, S1, 1)               2k+5
  (5) s=S1, R=2k+1           -> (1^(2k) ++ S0::l, S1, 0)             2k+3
  (6) s=S1, R=2k+2           -> (1^(2k) ++ S0::l, S1, 1)             2k+5

Note rules 3/4 and 5/6 share a prefix: R=2k+1 and R=2k+2 push the SAME
word onto l and differ only in the leftover R' (0 resp. 1) and in the
step count.  That is the parity structure section 8 warns to expect.

THE ONE PARTIAL RULE.  Rule 2 needs l to contain a S1.  On an all-blank
left half-tape `(l, S1, 0)` the machine sweeps left forever writing 1s and
never returns to StA -- so the macro system is PARTIAL, and any liveness
argument has to carry an invariant that excludes `l` all-zero.  This is the
same shape as M1/M4's "a D-free run from an arbitrary shaped configuration
does not terminate": the invariant is not decoration.

Usage:  python3 tools/mxdys4/cmacro2.py [nmacro]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Sim                                                # noqa: E402

CODE = '1RB0RB_0LC1RD_1LC1LA_0LA1RB'


def rule(l, s, R):
    """-> (name, cost, l', s', R') on the cconf triple, or None when the
    macro system is undefined (rule 2 with no S1 in l).  [l] is a list of
    0/1, NEAREST CELL FIRST."""
    if R == 0:
        if s == 0:                                        # rule 1
            return ('1', 3, l[1:], (l[0] if l else 0), 1)
        if 1 not in l:                                    # rule 2, diverges
            return None
        j = l.index(1)                                    # rule 2
        l1 = l[j + 1:]
        return ('2', j + 4, l1[1:], (l1[0] if l1 else 0), j + 2)
    k = (R - 1) // 2                                      # R = 2k+1 or 2k+2
    odd = (R % 2 == 1)
    if s == 0:
        pref = [1] * (2 * k + 1)                          # rules 3, 4
        name = '3' if odd else '4'
    else:
        pref = [1] * (2 * k) + [0]                        # rules 5, 6
        name = '5' if odd else '6'
    cost = (2 * k + 3) if odd else (2 * k + 5)
    return (name, cost, pref + l, 1, 0 if odd else 1)


def trim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def read_cconf(sim):
    """Read (l, s, R) off a raw simulator configuration in state A, and
    check the right half really is 1^R then blanks."""
    ks = [k for k, v in sim.tape.items() if v] or [sim.pos]
    lo = min(min(ks), sim.pos)
    hi = max(max(ks), sim.pos)
    l = trim([sim.tape[j] for j in range(sim.pos - 1, lo - 1, -1)])
    R = 0
    j = sim.pos + 1
    while sim.tape[j] == 1:
        R += 1
        j += 1
    while j <= hi:
        if sim.tape[j] != 0:
            return None                                   # right half impure
        j += 1
    return (l, sim.tape[sim.pos], R)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    sim = Sim(CODE)
    # advance to the first StA configuration
    while sim.st != 'A':
        sim.step()
    cur = read_cconf(sim)
    assert cur is not None, 'right half impure at the first StA'
    checked = impure = 0
    hist = []
    for i in range(n):
        l, s, R = cur
        r = rule(l, s, R)
        if r is None:
            print('macro system undefined at step %d: l=%s s=%d R=%d'
                  % (i, ''.join(map(str, l)) or '.', s, R))
            break
        name, cost, lp, sp, Rp = r
        # run the raw machine `cost` steps and compare
        for _ in range(cost):
            sim.step()
        if sim.st != 'A':
            print('MISMATCH at macro %d rule %s: raw state %s, expected A'
                  % (i, name, sim.st))
            return 1
        got = read_cconf(sim)
        if got is None:
            impure += 1
            print('MISMATCH at macro %d rule %s: right half not unary' % (i, name))
            return 1
        want = (trim(lp), sp, Rp)
        if got != want:
            print('MISMATCH at macro %d rule %s:\n  raw  l=%s s=%d R=%d\n'
                  '  rule l=%s s=%d R=%d'
                  % (i, name, ''.join(map(str, got[0])) or '.', got[1], got[2],
                     ''.join(map(str, want[0])) or '.', want[1], want[2]))
            return 1
        checked += 1
        hist.append((name, len(got[0]), got[2]))
        cur = got
    print('%s: %d macro steps, %d differentially validated against the raw '
          'simulator, 0 mismatches, 0 impure right halves.' % (CODE, n, checked))
    # rule histogram
    from collections import Counter
    c = Counter(h[0] for h in hist)
    print('rule firings: ' + '  '.join('%s:%d' % (k, c[k]) for k in sorted(c)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
