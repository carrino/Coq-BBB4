#!/usr/bin/env python3
"""The micro-lap of 1RB0RC_0LC1LB_0LD1LC_1RD0RA (wave4 #15), measured.

#15 is the mod-4 wave odometer.  Sampled at the LEFT RECORD -- head on the
leftmost visited cell, StC, reading blank, left list empty -- the tape is

    (StC, ([], S0, 1^lead 0 1^v0 0 1^v1 0 ... 0 1^vn 0))

with `lead` alternating 1 / 2 (BBB's lead-1/2 micro-period) and `v` the block
vector, frontier-first.  Two rules alternate:

  A  lead 1 -> 2:  v[0] += 1                                   10 steps
  B  lead 2 -> 1:  let i = least index with v[i] mod 4 /= 0
       i < last:  v[i] += 2, v[i+1] += 1         4*sum(v[..i]) + 4i + 18
       i = last:  v[i] += 1, append 2            4*sum(v[..i]) + 4i + 22

Rule B is the mod-4 analogue of `WaveCounter.carry`: the scan walks the
vector until it finds a block that is not 0 mod 4 and deposits there; at the
far end that deposit is a SPAWN (a new length-2 block), exactly as the mod-2
family's all-even case spawns a length-1 block.

TRAP, paid for once already: the branch is on the INDEX (`i < last` vs
`i = last`), NOT on the residue.  On the reachable orbit residue 1 only ever
occurs with `i < last` and residue 3 only with `i = last`, so fitting the
orbit alone suggests "residue 1 -> deposit, residue 3 -> spawn" -- and that
is wrong.  Probing off-orbit vectors settles it: `[4,3,2]` stops at `i=1`
with residue 3 and goes to `[4,5,3]`, the INTERIOR rewriting.  `probe_off()`
below keeps that honest.

Measured facts this file checks, over every anchor out to the step budget:

  * both rules and all three step counts, exactly (0 mismatches to t = 4e5);
  * the scan never runs off the end (some block is /= 0 mod 4);
  * the block at the stop is ODD.  An even stop (residue 2) is what the
    safety invariant has to exclude -- measured, the machine then leaves the
    anchor family altogether rather than taking either branch.

The TAPE-level pieces are checked too (`gadgets()` below), in the exact form
Coq will state them:

  ruleA   (StC,([],S0,      S1::S0::S1::R)) -10-> (StC,([],S0,S1::S1::S0::S1::S1::R))
  entry5  (StC,([],S0,      S1::S1::S0::R))  -5-> (StC,([S0;S0;S1;S1],S0,R))
  out6    (StC,(S0::L,S0,   S1::S1::S1::R))  -6-> (StC,(S0::S1::S1::L,S0,S1::R))
  carry5  (StC,(S0::L,S0,   S1::S1::S0::R))  -5-> (StC,(S0::S0::S1::S1::L,S0,R))
  ret1    (StC,(S1::L,S1,R))                 -1-> (StC,(L,S1,S1::R))
  cross7  (StC,(S0::S1::S1::L,S1,R))         -7-> (StC,(L,S1,S0::S1::S1::R))
  exit1   (StC,([],S1,R))                    -1-> (StC,([],S0,S1::R))

Rule A is a SINGLE uniform window -- no induction at all, which is why it is
constant-cost.  `out6` consumes three 1s and hands one back (net -2 per unit,
6 steps), so the outward sweep over a run of length 2k+1 is 6k steps and
leaves exactly one 1 -- and that ODD-length requirement is the tape-level
reason the invariant is mod 4 rather than mod 2.  `carry5` is John's "2 left
and it continues on" (it ends on A1 = 0RC, so the scan carries); the deposit
is his "1 left and it bounces" (A0 = 1RB fills the line and bounces right
into B).  `ret1` is the 1-step/cell return and `cross7` passes a line through
untouched, giving rule B's 3+1 = 4 steps per cell.

STILL OPEN -- the DEPOSIT.  It is `C0 . D0^2 . D1 . A0 . B1^k . B0` and the
`B1^k` walks back over the laid 1s until it meets a 0, so k depends on the
debris and the deposit is NOT a fixed window: stated as
`(StC,(S0::L,S0,S1::S0::R)) -8-> (StC,(S1::L,S1,S0::S1::R))` it matches every
config taken from a real trace, passes a sampled check, passes a naive
"does the tail pass through" window search -- and fails the EXHAUSTIVE check
on 496 of 961 contexts.  Prefixing the two debris shapes out6/entry5 actually
leave does not fix it.  That gadget, and the assembly, are what remain.

UNTRUSTED, like everything under tools/.  Usage: `python3 lap15.py [budget]`.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe15 import cstep, A, B, C, D, S0, S1, c0


def blocks(R):
    """Run lengths of the 1-runs of a right half-tape list."""
    out, i, n = [], 0, len(R)
    while i < n:
        if R[i] == S1:
            j = i
            while j < n and R[j] == S1:
                j += 1
            out.append(j - i)
            i = j
        else:
            i += 1
    return out


def anchors(budget):
    """Every left record, as (t, lead, vector)."""
    c, out = c0, []
    for t in range(budget):
        q, (L, h, R) = c
        if q == C and L == [] and h == S0 and R and R[0] == S1:
            b = blocks(R)
            out.append((t, b[0], b[1:]))
        c = cstep(c)
        if c is None:
            break
    return out


def stop(v):
    """(index, residue) of the first block that is not 0 mod 4."""
    for i, x in enumerate(v):
        if x % 4:
            return i, x % 4
    return None, None


def nextA(lead, v):
    """The abstract successor, and the step count it costs."""
    if lead == 1:
        return 2, [v[0] + 1] + v[1:], 10
    i, r = stop(v)
    assert i is not None, ('carry ran off the end', v)
    assert r % 2 == 1, ('the block at the stop is even', v)
    base = 4 * sum(v[:i + 1]) + 4 * i
    if i < len(v) - 1:
        return 1, v[:i] + [v[i] + 2, v[i + 1] + 1] + v[i + 2:], base + 18
    return 1, v[:i] + [v[i] + 1, 2], base + 22


def WInv4(v, p=0):
    """The safety invariant: walk the vector with a running parity bit.

    An even block must be 0 mod 4; an odd block must be 1 mod 4 when the
    parity so far is even and 3 mod 4 when it is odd; and the LAST block is
    2 mod 4 if the parity so far is odd, 3 mod 4 if it is even.  Equivalently
    (and this is the mod-2 family's `fp` in disguise): the number of ODD
    blocks is ODD, and the odd blocks read left to right alternate 1, 3, 1, 3
    mod 4.  It implies exactly what rule B needs -- the scan finds a block
    that is not 0 mod 4, and that block is odd, so the deposit is defined.
    """
    if not v:
        return False
    for k, x in enumerate(v):
        if k == len(v) - 1:
            return x % 4 == (2 if p else 3)
        if x % 2:
            if x % 4 != (3 if p else 1):
                return False
            p ^= 1
        elif x % 4 != 0:
            return False
    return False


def probe_off():
    """Off-orbit vectors: the branch is the index, and an even stop dies."""
    def anchor(v):
        R = [S1, S1, S0]
        for x in v:
            R += [S1] * x + [S0]
        return (C, ([], S0, R))

    def nxt(c, cap=8000):
        for t in range(1, cap):
            c = cstep(c)
            if c is None:
                return None, None
            q, (L, h, R) = c
            if q == C and L == [] and h == S0 and R and R[0] == S1:
                b = blocks(R)
                return t, (b[0], b[1:])
        return None, None
    bad = []
    # residue 3 at an INTERIOR stop takes the interior branch, not the spawn
    for v, want in [([4, 3, 2], [4, 5, 3]), ([3, 4, 2], [5, 5, 2]),
                    ([8, 3, 2], [8, 5, 3]), ([3, 2], [5, 3]),
                    ([4, 4, 5], [4, 4, 6, 2]), ([4, 4, 3], [4, 4, 4, 2])]:
        _, r = nextA(2, v)[0:1], None
        nl, nv, n = nextA(2, v)
        t, got = nxt(anchor(v))
        if got is None or got[1] != want or nv != want or t != n:
            bad.append('off-orbit %s -> %s (predicted %s, %s steps)' % (v, got, nv, n))
    # an EVEN stop leaves the anchor family: no next left record at all
    for v in [[4, 2], [4, 4, 2], [2, 4, 2], [6, 4, 2], [4, 6, 2], [4, 4, 4]]:
        t, got = nxt(anchor(v))
        if t is not None:
            bad.append('even stop %s unexpectedly returned to an anchor' % v)
    return bad


def gadgets():
    """The tape-level windows, EXHAUSTIVELY checked over every (L, R) with
    |L|, |R| <= 4 -- 961 contexts each, not a spot-check.

    That distinction is not pedantry: `turn8` below (the deposit) passes a
    sampled check and a naive "does the tail pass through" window search, and
    fails the exhaustive one on 496 of 961.  Its bounce walks back over the
    laid 1s until it meets a 0, so its length depends on the debris and it is
    NOT a fixed window.  Every other piece is genuinely uniform.
    """
    import itertools
    allX = [list(x) for n in range(0, 5)
            for x in itertools.product([S0, S1], repeat=n)]
    bad = []

    def T(n, c):
        for _ in range(n):
            c = cstep(c)
            if c is None:
                return None
        return c

    def chk(nm, n, mk, want):
        for L in allX:
            for R in allX:
                if T(n, mk(L, R)) != want(L, R):
                    bad.append(nm)
                    return
    chk('entry5', 5, lambda L, R: (C, ([], S0, [S1, S1, S0] + R)),
        lambda L, R: (C, ([S0, S0, S1, S1], S0, R)))
    chk('out6', 6, lambda L, R: (C, ([S0] + L, S0, [S1, S1, S1] + R)),
        lambda L, R: (C, ([S0, S1, S1] + L, S0, [S1] + R)))
    chk('carry5', 5, lambda L, R: (C, ([S0] + L, S0, [S1, S1, S0] + R)),
        lambda L, R: (C, ([S0, S0, S1, S1] + L, S0, R)))
    chk('ret1', 1, lambda L, R: (C, ([S1] + L, S1, R)),
        lambda L, R: (C, (L, S1, [S1] + R)))
    chk('cross7', 7, lambda L, R: (C, ([S0, S1, S1] + L, S1, R)),
        lambda L, R: (C, (L, S1, [S0, S1, S1] + R)))
    chk('exit1', 1, lambda L, R: (C, ([], S1, R)),
        lambda L, R: (C, ([], S0, [S1] + R)))
    chk('ruleA', 10, lambda L, R: (C, ([], S0, [S1, S0, S1] + R)),
        lambda L, R: (C, ([], S0, [S1, S1, S0, S1, S1] + R)))
    return bad


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    rows = anchors(budget)
    bad, kinds, maxi = [], {}, 0
    for k in range(len(rows) - 1):
        (t, lead, v), (t2, lead2, v2) = rows[k], rows[k + 1]
        if not v:
            continue          # the boot anchor, before the vector exists
        if lead == 2:
            i, r = stop(v)
            kinds[r] = kinds.get(r, 0) + 1
            maxi = max(maxi, i if i is not None else 0)
        try:
            nl, nv, n = nextA(lead, v)
        except AssertionError as e:
            bad.append('t=%d %s: %s' % (t, v, e.args[0]))
            continue
        if (nl, nv) != (lead2, v2):
            bad.append('t=%d lead=%d %s -> %s, predicted %d %s'
                       % (t, lead, v, v2, nl, nv))
        elif t2 - t != n:
            bad.append('t=%d lead=%d %s: %d steps, predicted %d'
                       % (t, lead, v, t2 - t, n))
    print('#15 micro-lap over %d anchors (t <= %d)' % (len(rows), rows[-1][0]))
    print('  rule-B stops by residue: %s   deepest scan: index %d'
          % (kinds, maxi))
    for m in bad[:8]:
        print('  FAIL %s' % m)
    inv = sum(1 for (t, l, v) in rows if v and WInv4(v if l == 2 else [v[0] + 1] + v[1:]))
    tot = sum(1 for (t, l, v) in rows if v)
    print('  invariant WInv4 holds on %d / %d anchors' % (inv, tot))
    if inv != tot:
        bad.append('WInv4 does not hold on every anchor')
    g = gadgets()
    print('  tape-level gadgets: %s' % ('OK' if not g else 'FAIL ' + ', '.join(g)))
    bad += g
    o = probe_off()
    print('  off-orbit branch/death: %s' % ('OK' if not o else 'FAIL ' + ', '.join(o)))
    bad += o
    for m in bad[:8]:
        print('  FAIL %s' % m)
    print('#15 lap: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
