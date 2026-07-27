#!/usr/bin/env python3
"""Step 0 for boarding tower #20: replay the lap using ONLY the verified
gadgets, symbolically, and diff it against the real machine.

`lap20.py` verifies each gadget in isolation.  That is not enough to write the
Coq: the LAP is a composition, and the composition is where the block word has
to line up.  This file composes the gadgets as pure list operations -- it never
calls `cstep` to build a state -- and then checks the result against
`probe20`'s raw simulator, step count AND configuration, for every r.

If this is green the Coq lap proof is a transcription: the gadget sequence
printed by `trace(r)` IS the proof script, and the regular structure in it is
the induction.

THE SHAPE.  The anchors are the StC left records, and they alternate

    A(r,rest)  (StC, ([], S0, 1 1 0 1 0     ++ b^r ++ rest))
    B(r,rest)  (StC, ([], S0, 1 0 1 1 1 1 0 ++ b^r ++ rest))    b = 110

`ruleA` is A -> B in a constant 10 steps.  The long lap B(r,rest) ->
A(r+1,rest') is four phases:

  1. entry10  (StC,([],S0,1011110++T)) -10-> (StC,([1,0,1,0,1,1],S0,1++T))
     -- a uniform window; T is the whole rest of the tape.  The left debris
     E = [1,0,1,0,1,1] is what makes the lap `r -> r+1` (see phase 4).
  2. out5^r   eats the b-run one block at a time, laying [1,0,1] per block:
     after it the left list is (101)^r ++ E and the right list is 1 ++ rest.
     That (101)^r is John's "repeated 101" -- the empty bouncer body.
  3. THE MIDDLE.  The outward sweep runs on into `rest` (StA/StD alternating
     rightward: A1 = 0RD writes a 0, D1 = 1RA writes a 1, so it lays a UNARY
     run), turns around, and hands back to StC with head S1.
  4. THE RETURN, which is the re-encoder: `rb3` eats [1,0,1] off the left and
     emits the block b = 110; `rb2` eats [0,1] and emits a = 10.  ONE BLOCK
     PER UNIT -- this is why the alphabet is real and not a way of looking at
     the tape.  Running it over (101)^r ++ E emits

         b^r  then  b, a, b   (E = [1,0,1] ++ [0,1] ++ [1])

     and since emissions push onto the FRONT of R the tape comes out as
     b :: a :: b^r :: ... = 1 1 0 1 0 ++ b^r ++ ... -- the A-type lead with
     the b-run one longer.  The +1 of the counter is exactly the spare b in
     the entry debris.

Gadgets used, all checked EXHAUSTIVELY over every (L,R) with |L|,|R| <= 4 by
`lap20.py` (961 contexts -- the standard #15's deposit failed on 496 of):

    out5    (StC,(L,S0,       1 1 1 0 ++ R)) -5-> (StC,(1 0 1 ++ L, S0, 1 ++ R))
    cross5  (StC,(L,S0,       1 1 0 1 ++ R)) -5-> (StB,(1 0 1 ++ L, S1, 1 ++ R))
    ret3    (StB,(1 1 0 ++ L, S1,        R)) -3-> (StB,(L, S0, 1 1 1 ++ R))
    ret2    (StB,(1 0   ++ L, S1,        R)) -2-> (StB,(L, S0, 1 1   ++ R))
    rb3     (StC,(1 0 1 ++ L, S1,        R)) -3-> (StC,(L, S1, 1 1 0 ++ R))
    rb2     (StC,(0 1   ++ L, S1,        R)) -2-> (StC,(L, S1, 1 0   ++ R))

plus the single-step joints (the transition table, one `reflexivity` each in
Coq), which is all the MIDDLE is built from -- like #15's deposit, it is a
SWEEP whose length is discovered by the walk, not a fixed window.

UNTRUSTED, like everything under tools/.  Usage: `python3 asm20.py [maxr]`.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe20 import cstep, chd, ctl, A, B, C, D, S0, S1

NM = 'ABCD'

LEAD_A = [S1, S1, S0, S1, S0]
LEAD_B = [S1, S0, S1, S1, S1, S1, S0]
BLK = [S1, S1, S0]
ENTRY_DEBRIS = [S1, S0, S1, S0, S1, S1]


# -- the single-step joints (the transition table; a reflexivity each in Coq)
def jca(s): q, L, h, R = s; return (A, [S1] + L, chd(R), ctl(R))   # C0 = 1RA
def jcb(s): q, L, h, R = s; return (B, ctl(L), chd(L), [S0] + R)   # C1 = 0LB
def jad(s): q, L, h, R = s; return (D, [S0] + L, chd(R), ctl(R))   # A1 = 0RD
def jab(s): q, L, h, R = s; return (B, [S1] + L, chd(R), ctl(R))   # A0 = 1RB
def jda(s): q, L, h, R = s; return (A, [S1] + L, chd(R), ctl(R))   # D1 = 1RA
def jdc(s): q, L, h, R = s; return (C, ctl(L), chd(L), [S1] + R)   # D0 = 1LC
def jbb(s): q, L, h, R = s; return (B, ctl(L), chd(L), [S1] + R)   # B1 = 1LB
def jbc(s): q, L, h, R = s; return (C, ctl(L), chd(L), [S1] + R)   # B0 = 1LC


def anchor(r, rest, kind='A'):
    """A(r,rest) / B(r,rest), built from the block word -- not the simulator."""
    lead = LEAD_A if kind == 'A' else LEAD_B
    return (C, [], S0, lead + BLK * r + list(rest))


# -- the verified windows, as pure list operations
def g_entry10(s):
    q, L, h, R = s
    return (C, list(ENTRY_DEBRIS) + L, S0, [S1] + R[7:]), 10


def g_out5(s):
    q, L, h, R = s
    return (C, [S1, S0, S1] + L, S0, [S1] + R[4:]), 5


def g_cross5(s):
    q, L, h, R = s
    return (B, [S1, S0, S1] + L, S1, [S1] + R[4:]), 5


def g_ret3(s):
    q, L, h, R = s
    return (B, L[3:], S0, [S1, S1, S1] + R), 3


def g_ret2(s):
    q, L, h, R = s
    return (B, L[2:], S0, [S1, S1] + R), 2


def g_rb3(s):
    """(StC,(1::M,S1,R)) with chd M = S0.  Stated through chd/ctl so the END of
    the left list -- L = [1], the exit onto the new anchor -- is not a
    separate case."""
    q, L, h, R = s
    N = ctl(L[1:])
    return (C, ctl(N), chd(N), [S1, S1, S0] + R), 3


def g_rb2(s):
    """(StC,(0::M,S1,R)); likewise through chd/ctl."""
    q, L, h, R = s
    M = L[1:]
    return (C, ctl(M), chd(M), [S1, S0] + R), 2


def g_step(nm, f):
    return lambda s: (f(s), 1)


GADGETS = [
    ('entry10', lambda s: s[0] == C and s[1] == [] and s[2] == S0
                and s[3][:7] == LEAD_B, g_entry10),
    ('out5', lambda s: s[0] == C and s[2] == S0
             and s[3][:4] == [S1, S1, S1, S0], g_out5),
    ('cross5', lambda s: s[0] == C and s[2] == S0
               and s[3][:4] == [S1, S1, S0, S1], g_cross5),
    ('ret3', lambda s: s[0] == B and s[2] == S1
             and s[1][:3] == [S1, S1, S0], g_ret3),
    ('ret2', lambda s: s[0] == B and s[2] == S1
             and s[1][:2] == [S1, S0], g_ret2),
    ('rb3', lambda s: s[0] == C and s[2] == S1
            and s[1][:1] == [S1] and chd(s[1][1:]) == S0, g_rb3),
    ('rb2', lambda s: s[0] == C and s[2] == S1 and s[1][:1] == [S0], g_rb2),
    # the MIDDLE: the transition table, one step at a time
    ('ca', lambda s: s[0] == C and s[2] == S0, g_step('ca', jca)),
    ('cb', lambda s: s[0] == C and s[2] == S1, g_step('cb', jcb)),
    ('ad', lambda s: s[0] == A and s[2] == S1, g_step('ad', jad)),
    ('ab', lambda s: s[0] == A and s[2] == S0, g_step('ab', jab)),
    ('da', lambda s: s[0] == D and s[2] == S1, g_step('da', jda)),
    ('dc', lambda s: s[0] == D and s[2] == S0, g_step('dc', jdc)),
    ('bb', lambda s: s[0] == B and s[2] == S1, g_step('bb', jbb)),
    ('bc', lambda s: s[0] == B and s[2] == S0, g_step('bc', jbc)),
]


def is_anchor(s):
    return s[0] == C and s[1] == [] and s[2] == S0


def norm(xs):
    xs = list(xs)
    while xs and xs[-1] == S0:
        xs.pop()
    return xs


def replay(r, rest, cap=200000):
    """Compose gadgets from B(r,rest) until the next left record.  Pure list
    ops -- `cstep` is never called."""
    s = anchor(r, rest, 'B')
    seq, total = [], 0
    for _ in range(cap):
        hit = None
        for (nm, m, f) in GADGETS:
            if m(s):
                hit = (nm, f)
                break
        if hit is None:
            return None, seq, total, 'stuck at %s' % NM[s[0]]
        s, n = hit[1](s)
        seq.append(hit[0])
        total += n
        if is_anchor(s) and total > 0:
            return s, seq, total, None
    return None, seq, total, 'cap'


def replay_ruleA(r, rest):
    """A(r,rest) -10-> B(r,rest): one constant uniform window."""
    q, L, h, R = anchor(r, rest, 'A')
    return (C, [], S0, LEAD_B + R[5:]), 10


def real(s, cap=2000000):
    """The same lap from the raw simulator, and every left record inside it."""
    c = (s[0], (list(s[1]), s[2], list(s[3])))
    inner = []
    for t in range(1, cap):
        c = cstep(c)
        if c is None:
            return None, None, inner
        q, (L, h, R) = c
        if q == C and L == [] and h == S0:
            return t, (q, L, h, norm(R)), inner
        if q == C and not norm(L) and h == S0:
            inner.append(t)
    return None, None, inner


def orbit_anchors(budget=400000):
    """Every settled StC left record from the real orbit, as (r, rest)."""
    from probe20 import c0
    c, out = c0, []
    for t in range(budget):
        q, (L, h, R) = c
        if L == [] and q == C and h == S0:
            out.append((t, norm(R)))
        c = cstep(c)
        if c is None:
            break
    la = LEAD_A
    st = next(i for i, (t, R) in enumerate(out) if R[:5] == la)
    rows = []
    for (t, R) in out[st:]:
        kind = 'A' if R[:5] == LEAD_A else 'B'
        body = R[5:] if kind == 'A' else R[7:]
        r = 0
        while body[:3] == BLK:
            r += 1
            body = body[3:]
        rows.append((t, kind, r, body))
    return rows


def compress(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%s^%d' % (a, b) if b > 1 else a for a, b in out)


def main():
    maxr = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    rows = orbit_anchors()
    bad, nlaps = [], 0

    # 1. rule A, against the orbit
    for i in range(0, min(len(rows) - 1, 2 * maxr), 2):
        (t, k, r, body) = rows[i]
        if k != 'A':
            bad.append('anchor %d is not A-type' % i)
            break
        got, n = replay_ruleA(r, body)
        tw, kw, rw, bw = rows[i + 1]
        if n != tw - t:
            bad.append('r=%d ruleA: %d steps, machine says %d' % (r, n, tw - t))
        if norm(got[3]) != norm(LEAD_B + BLK * rw + bw):
            bad.append('r=%d ruleA: config mismatch' % r)
    print('#20 rule A replayed from the window, %d anchors: %s'
          % (min(len(rows) // 2, maxr), 'OK' if not bad else bad[0]))

    # 2. the long lap, against the orbit
    lbad = []
    for i in range(1, min(len(rows) - 1, 2 * maxr), 2):
        (t, k, r, body) = rows[i]
        if k != 'B':
            lbad.append('anchor %d is not B-type' % i)
            break
        got, seq, n, err = replay(r, body)
        tw, kw, rw, bw = rows[i + 1]
        nlaps += 1
        if err:
            lbad.append('r=%d: %s' % (r, err))
            continue
        if n != tw - t:
            lbad.append('r=%d: %d steps, machine says %d' % (r, n, tw - t))
        elif norm(got[3]) != norm(LEAD_A + BLK * rw + bw):
            lbad.append('r=%d: config mismatch\n   got  %s\n   want %s'
                        % (r, norm(got[3]), norm(LEAD_A + BLK * rw + bw)))
        elif rw != r + 1:
            lbad.append('r=%d: the lap did not increment the b-run (%d)' % (r, rw))
        if len(lbad) > 3:
            break
    print('#20 long lap replayed from the gadgets alone, %d laps '
          '(config + step count + r -> r+1): %s'
          % (nlaps, 'OK' if not lbad else lbad[0]))
    bad += lbad

    # 3. no earlier anchor inside a lap
    ibad = []
    for i in range(0, min(len(rows) - 1, 2 * maxr)):
        (t, k, r, body) = rows[i]
        s = anchor(r, body, k)
        tt, cc, inner = real(s)
        if inner:
            ibad.append('anchor %d (%s r=%d): %d interior left records'
                        % (i, k, r, len(inner)))
            break
    print('#20 no earlier left record occurs inside a lap: %s'
          % ('OK' if not ibad else ibad[0]))
    bad += ibad

    # 4. the sequence, which is the proof script
    if not bad:
        print()
        print('  the gadget sequence (this is the Coq proof script):')
        for i in (1, 3, 5, 7, 9, 11, 15, 21):
            if i >= len(rows):
                break
            (t, k, r, body) = rows[i]
            _, seq, n, _ = replay(r, body)
            print('   r=%-3d n=%-5d %s' % (r, n, compress(seq)))

    print('#20 assembly: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
