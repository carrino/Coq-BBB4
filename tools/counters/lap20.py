#!/usr/bin/env python3
"""Reconnaissance checker for tower #20 (1RB0RD_1LC1LB_1RA0LB_1LC1RA).

The measured facts this file pins, all against the CTape-faithful mirror
`probe20.py`:

  1. SAMPLING.  Read at the LEFT RECORD -- head on the leftmost visited
     cell, StC, reading blank, left list empty -- exactly as wave4 #15 and
     double #32 are read.  The anchors come in alternating pairs:

        A-type   (StC, ([], S0, 1 1 0 1 0     ++ T))
        B-type   (StC, ([], S0, 1 0 1 1 1 1 0 ++ T))

     with the SAME T.  So the lead alternates, exactly like #15's 1/2.

  2. RULE A IS A CONSTANT 10-STEP UNIFORM WINDOW.  A-type -> B-type in ten
     steps, for EVERY tail, checked over all 511 tails with |T| <= 8 (and
     the machine's left list is empty at both ends, so there is no L to
     quantify over).  This is #15's `ruleA` again: constant cost, no
     induction, and it is the whole of the no-carry lap.

  3. JOHN'S ALPHABET.  The tape after the lead factors greedily into the
     blocks 110 (call it `b`) and 10 (`a`).  When the residue is exactly
     `1` the WHOLE tape is a block word -- and those configurations are
     precisely the sparse anchors (t = 142, 626, 1750, ...) whose words are
        b a b^(2^k) <pat>
     i.e. BBB's `pat ++ (2)^r ++ [1]` with the macro symbol 2 = 110.

  4. THE COUNTER.  At every A-type anchor the block word after the lead
     starts with a run of `b`s, and THAT RUN LENGTH IS THE LAP INDEX: it is
     0, 1, 2, 3, ... with no exceptions over the anchors reachable in
     400,000 steps.  So one long lap is `r -> r+1` and the abstract state is
     `(r, rest)` -- `WaveCounter.wglue_neverqh`'s interface (an arbitrary
     anchor type with a total successor and a preserved invariant), which is
     the closer double #32 used.  No closed form for `rest` is needed.

  STILL OPEN, and it is the whole remaining job: the long lap's tape-level
  gadgets.  Per the trap #15 paid for, they must be checked EXHAUSTIVELY
  over every (L,R) with |L|,|R| <= 4 before any Coq is written -- a sampled
  check is not a check.

UNTRUSTED, like everything under tools/.  Usage: `python3 lap20.py [budget]`.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe20 import cstep, csteps, c0, S0, S1

C = 2

LEAD_A = [S1, S1, S0, S1, S0]
LEAD_B = [S1, S0, S1, S1, S1, S1, S0]


def blocks(s):
    """Greedy 110/10 factorisation from the left; returns (word, residue)."""
    out, i = [], 0
    while i < len(s):
        if s[i:i + 3] == '110':
            out.append('b'); i += 3
        elif s[i:i + 2] == '10':
            out.append('a'); i += 2
        else:
            break
    return ''.join(out), s[i:]


def anchors(budget):
    """Every StC left record, as (t, tape-string-right-of-the-head)."""
    c, out = c0, []
    for t in range(budget):
        q, (L, h, R) = c
        if L == [] and q == C and h == S0:
            out.append((t, ''.join(map(str, R)).rstrip('0')))
        c = cstep(c)
        if c is None:
            break
    return out


def rule_a():
    """A-type -> B-type is ONE uniform 10-step window, every tail."""
    bad = []
    for k in range(0, 9):
        for T in itertools.product([S0, S1], repeat=k):
            T = list(T)
            got = csteps(10, (C, ([], S0, LEAD_A + T)))
            want = (C, ([], S0, LEAD_B + T))
            if got != want:
                bad.append('T=%s' % T)
    return bad


def settled(rows):
    """The anchor family starts once the leads settle -- the first three left
    records (t = 4, 18, 28) are the boot and belong to no phase."""
    la = ''.join(map(str, LEAD_A))
    for i, (t, s) in enumerate(rows):
        if s.startswith(la):
            return rows[i:]
    return []


def leads(rows):
    """Every anchor is A-type or B-type, and they strictly alternate."""
    bad, kind = [], []
    for (t, s) in rows:
        a = s.startswith(''.join(map(str, LEAD_A)))
        b = s.startswith(''.join(map(str, LEAD_B)))
        if a == b:
            bad.append('t=%d: lead is neither/both: %s' % (t, s[:12]))
        kind.append('A' if a else 'B')
    for i in range(1, len(kind)):
        if kind[i] == kind[i - 1]:
            bad.append('leads do not alternate at index %d' % i)
            break
    return bad


def counter(rows):
    """The leading b-run at the A-type anchors IS the lap index."""
    bad, runs = [], []
    for (t, s) in rows:
        if not s.startswith(''.join(map(str, LEAD_A))):
            continue
        w, _ = blocks(s[len(LEAD_A):])
        runs.append(len(w) - len(w.lstrip('b')))
    for i, r in enumerate(runs):
        if r != i:
            bad.append('b-run at A-anchor %d is %d, not %d' % (i, r, i))
            break
    return bad, runs


def pure(rows):
    """The tapes that are a WHOLE block word -- John's reading -- and their
    words.  These are the sparse 'tower' anchors."""
    out = []
    for (t, s) in rows:
        w, res = blocks(s)
        if res == '1':
            out.append((t, w))
    return out


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    allrows = anchors(budget)
    rows = settled(allrows)
    bad = []
    print('#20 boot: %d left records before the family settles (first anchor t=%d)'
          % (len(allrows) - len(rows), rows[0][0]))

    e = rule_a()
    print('#20 rule A (10 steps, uniform over all |T| <= 8): %s'
          % ('OK' if not e else '%d FAILURES' % len(e)))
    bad += e

    e = leads(rows)
    print('#20 leads alternate 11010 / 1011110 over %d anchors: %s'
          % (len(rows), 'OK' if not e else e[0]))
    bad += e

    e, runs = counter(rows)
    print('#20 leading b-run = lap index over %d A-anchors: %s'
          % (len(runs), 'OK' if not e else e[0]))
    bad += e

    p = pure(allrows)
    print('#20 whole-tape block words (the tower anchors): %d found' % len(p))
    for (t, w) in p[:5]:
        print('   t=%-7d %s' % (t, w[:72]))

    print('#20 recon: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
