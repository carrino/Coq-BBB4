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

  5. FOUR GADGETS OF THE LONG LAP, each checked EXHAUSTIVELY over every
     (L,R) with |L|,|R| <= 4 (961 contexts, the standard #15's deposit
     failed on 496 of):

       out5    (StC,(L,S0,       1 1 1 0 ++ R)) -5-> (StC,(1 0 1 ++ L, S0, 1 ++ R))
       cross5  (StC,(L,S0,       1 1 0 1 ++ R)) -5-> (StB,(1 0 1 ++ L, S1, 1 ++ R))
       ret3    (StB,(1 1 0 ++ L, S1,        R)) -3-> (StB,(L, S0, 1 1 1 ++ R))
       ret2    (StB,(1 0 ++ L,   S1,        R)) -2-> (StB,(L, S0, 1 1 ++ R))

     -- #15's shape exactly: the outward sweep eats four cells and hands one
     back (net +3 per five steps), `cross5` is the turnaround into StB, and
     the return is ONE STEP PER CELL filling with 1s.  The two remaining
     joints (B0 = 1LC and C1 = 0LB) read `chd L`, so like #15's they have to
     be stated through chd/ctl rather than as windows.

  6. WHAT THE TWO SWEEPS ARE, read straight off the transition table
     (A0=1RB A1=0RD, B0=1LC B1=1LB, C0=1RA C1=0LB, D0=1LC D1=1RA):

       OUTWARD.  StA and StD alternate RIGHTWARD over a run of 1s --
       A1 = 0RD writes a 0, D1 = 1RA writes a 1 -- so the outward sweep
       LAYS STRIPES, two cells per two steps.  It ends at a 0: D0 = 1LC
       turns around into StC, and StC either continues right (C0 = 1RA)
       or drops into the return (C1 = 0LB).  `out5` and `cross5` above are
       this alternation packaged over one block.

       RETURN.  StB walks LEFTWARD filling with 1s (B1 = 1LB), and at a 0
       it writes 1 and hands to StC (B0 = 1LC); StC at a 1 writes 0 and
       hands back to StB (C1 = 0LB).  So the return RE-STRIPES what the
       outward sweep laid, one step per cell, and it stops when StC meets
       a 0 (C0 = 1RA).  `ret3`/`ret2` are this over one block.

     That is #15's outward/return pair with the roles of the states
     permuted, which is what John's "the head bounces off of the lsb and
     then passes through" describes.

  STILL OPEN: the assembly -- an `asm20.py` in the shape of `asm15.py`, i.e.
  replay the lap from these gadgets alone as pure list ops and diff it
  against the raw simulator for every r.  That is the gate the Coq is a
  transcription of.  Then the invariant on `rest`, and the step count (the
  long lap costs 36, 56, 52, 72, 68, 84, 84, 124, ... for r = 1,2,3,...).
  Do NOT write Coq from a sampled check: that is the trap #15 paid for.

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


GADGETS = [
    ('out5   (StC,(L,S0,1110++R))', 5, C, [], S0, [S1, S1, S1, S0]),
    ('cross5 (StC,(L,S0,1101++R))', 5, C, [], S0, [S1, S1, S0, S1]),
    ('ret3   (StB,(110++L,S1,R))', 3, 1, [S1, S1, S0], S1, []),
    ('ret2   (StB,(10++L,S1,R))', 2, 1, [S1, S0], S1, []),
]


def exhaustive(n, q, preL, head, preR, maxlen=4):
    """Run the window over EVERY (L,R) with |L|,|R| <= maxlen and report
    whether the context passes through untouched and the core is uniform."""
    res = set()
    for kl in range(maxlen + 1):
        for Lx in itertools.product([S0, S1], repeat=kl):
            for kr in range(maxlen + 1):
                for Rx in itertools.product([S0, S1], repeat=kr):
                    Lx, Rx = list(Lx), list(Rx)
                    g = csteps(n, (q, (preL + Lx, head, preR + Rx)))
                    if g is None:
                        return None, 'dies'
                    gq, (gL, gh, gR) = g
                    if kl and gL[-kl:] != Lx:
                        return None, 'left context consumed'
                    if kr and gR[-kr:] != Rx:
                        return None, 'right context consumed'
                    res.add((gq, tuple(gL[:len(gL) - kl]), gh,
                             tuple(gR[:len(gR) - kr])))
    return res, ('uniform' if len(res) == 1 else '%d distinct cores' % len(res))


def gadgets():
    """Every long-lap gadget, over all 961 contexts with |L|,|R| <= 4."""
    bad = []
    for (nm, n, q, pl, h, pr) in GADGETS:
        r, m = exhaustive(n, q, pl, h, pr)
        if m != 'uniform':
            bad.append('%s: %s' % (nm, m))
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

    e = gadgets()
    print('#20 long-lap gadgets, EXHAUSTIVE over all 961 (L,R) with |L|,|R| <= 4: %s'
          % ('OK (out5, cross5, ret3, ret2)' if not e else e[0]))
    bad += e

    p = pure(allrows)
    print('#20 whole-tape block words (the tower anchors): %d found' % len(p))
    for (t, w) in p[:5]:
        print('   t=%-7d %s' % (t, w[:72]))

    print('#20 recon: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
