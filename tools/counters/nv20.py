#!/usr/bin/env python3
"""The ABSTRACT SUCCESSOR for tower #20, in closed form, and its validation.

`asm20.py` shows the lap is a composition of the verified gadgets.  This file
goes one level up: it gives the lap's action on the ABSTRACT STATE as a
closed-form total function, which is what `WaveCounter.wglue_neverqh`'s
`nextA` has to be.

THE STATE.  Sample at the A-type left record.  The tape is

    (StC, ([], S0, 1 1 0 1 0 ++ wruns w))        wruns [n1;n2;...] = 1^n1 0 1^n2 0 ...

so the abstract state is just the RUN-LENGTH WORD `w` of the tail.  There is
no separate lap index: the leading b-run of the block reading is exactly the
leading run of 2s of `w` (b = 110 = 1^2 0), so `blks r X = wruns (2^r ++ v)`
and `r` is recoverable, not carried.

THE SUCCESSOR.  Reading the tape rightward from the anchor the head enters on
a 1, so the run it actually reads at `n_i` is `n_i + 1`.  Hence

    n_i EVEN -> the run read is odd, the sweep RIDES over it and continues;
    n_i ODD  -> the run read is even, and that is the TURNAROUND.

-- wave4 #15's carry with the parities swapped.  Each ride lays an
alternating block that the return sweep re-encodes as `b a^(n/2 - 1)`, the
turn lays `a^((n-1)/2)`, and the entry debris contributes the spare `b` that
is the counter's +1.  Re-encoding reverses the unit order and maps
`b -> 2`, `a -> 1`, which gives

    nv  w = 2 :: nv0 w
    nv0 []          = []                           (excluded by the invariant)
    nv0 (n :: t)    = 1^(n/2 - 1) ++ 2 :: nv0 t             n EVEN
    nv0 (n :: [])   = 1^((n-1)/2) ++ [2; 1]                 n ODD
    nv0 (n::n2::t2) = 1^((n-1)/2) ++ (n2 + 3) :: t2         n ODD

`nv0` is a structural recursion on the list, so `nv` is TOTAL -- no fuel and
no closed form for the tape is needed anywhere.

VALIDATED: `nv` reproduces the orbit's A-anchor word exactly, for all 302
laps reachable in 400,000 steps, and on synthetic anchors built from an
arbitrary `w` (see `main`).

THE ONE THING THAT IS NOT SETTLED is the INVARIANT.  The lap needs the sweep
to turn, i.e. `w` must contain an ODD entry -- beyond the end of the tape
every run has length 0, which is even, so a word of all-even entries would
send the head off to the right for ever.  "Contains an odd" is TRUE on every
reachable word but is NOT preserved by `nv` on arbitrary words:

    nv [5;1] = [2;1;1;4]   and   nv [2;1;1;4] = [2;2;4;4]   -- no odd left

so `[5;1]` is not reachable, and a genuine strengthening is required.  Three
natural candidates are refuted here, with witnesses:

    "last entry is 1"                 -- nv [3;1] = [2;1;4]
    "nv0 w contains an odd"           -- nv [5;1] = [2;1;1;4]
    "last = 1 and the first odd is
     not second-to-last"              -- nv [1;1;2;3;1] = [2;4;2;3;1]

That predicate is the last thing standing between this file and the board.

UNTRUSTED, like everything under tools/.  Usage: `python3 nv20.py [budget]`.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe20 import cstep, c0, S0, S1

C = 2
LEAD_A = [S1, S1, S0, S1, S0]


def wruns(w):
    """1^n1 0 1^n2 0 ... -- the tape the run-length word names."""
    out = []
    for n in w:
        out += [S1] * n + [S0]
    return out


def runs(x):
    """The inverse, on a tape with the trailing blanks stripped."""
    x = list(x)
    while x and x[-1] == S0:
        x.pop()
    out, i = [], 0
    while i < len(x):
        n = 0
        while i < len(x) and x[i] == S1:
            n += 1
            i += 1
        out.append(n)
        if i < len(x):
            i += 1
    return out


def nv0(w):
    """The successor's body.  A structural recursion on the list, written as
    a loop here only to keep Python's stack out of it."""
    out = []
    while True:
        if not w:
            return out
        n, t = w[0], w[1:]
        if n % 2 == 0:
            out += [1] * (n // 2 - 1) + [2]
            w = t
            continue
        if not t:
            return out + [1] * (n // 2) + [2, 1]
        return out + [1] * (n // 2) + [t[0] + 3] + t[1:]


def nv(w):
    """One lap on the abstract state.  The leading 2 is the entry debris's
    spare block -- the counter's +1."""
    return [2] + nv0(w)


def orbit(budget):
    """The A-type left records, as run-length words."""
    c, out = c0, []
    for t in range(budget):
        q, (L, h, R) = c
        if L == [] and q == C and h == S0:
            s = ''.join(map(str, R)).rstrip('0')
            if s.startswith('11010'):
                out.append((t, runs([int(x) for x in s[5:]])))
        c = cstep(c)
        if c is None:
            break
    return out


def lap_from(w, cap=4000000):
    """Run the machine from the synthetic A-anchor named by w to the NEXT
    A-type left record, and read the word back off the tape."""
    c = (C, ([], S0, LEAD_A + wruns(w)))
    seen = 0
    for t in range(1, cap):
        c = cstep(c)
        if c is None:
            return None
        q, (L, h, R) = c
        if q == C and L == [] and h == S0:
            s = ''.join(map(str, R)).rstrip('0')
            if s.startswith('11010'):
                return runs([int(x) for x in s[5:]])
            seen += 1
            if seen > 2:
                return None
    return None


def hasodd(w):
    return any(x % 2 for x in w)


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    rows = orbit(budget)
    bad = []

    # 1. nv against the real orbit
    n = 0
    for i in range(len(rows) - 1):
        n += 1
        if nv(rows[i][1]) != rows[i + 1][1]:
            bad.append('t=%d: nv(%s) = %s, orbit says %s'
                       % (rows[i][0], rows[i][1][:8], nv(rows[i][1])[:8],
                          rows[i + 1][1][:8]))
            break
    print('#20 nv against the orbit, %d laps: %s'
          % (n, 'OK' if not bad else bad[0]))

    # 2. nv against synthetic anchors -- states the orbit never visits
    synth = [[1, 4], [7], [3], [5], [9], [1, 1], [3, 1], [5, 1], [7, 1],
             [2, 1], [4, 1], [2, 2, 1], [4, 4, 1], [2, 1, 1], [6, 1], [8, 1],
             [2, 2, 1, 2, 1], [2, 2, 2, 3, 1], [2, 2, 3, 1], [1, 2, 3, 1],
             [3, 2, 1], [2, 3, 1], [1, 2, 2, 1], [4, 2, 2, 1], [5, 2, 2, 1]]
    sbad = []
    for w in synth:
        got = lap_from(w)
        if got is None:
            sbad.append('%s: no A-type record' % w)
        elif got != nv(w):
            sbad.append('%s: machine gives %s, nv gives %s' % (w, got, nv(w)))
        if len(sbad) > 3:
            break
    print('#20 nv against %d synthetic anchors: %s'
          % (len(synth), 'OK' if not sbad else sbad[0]))
    bad += sbad

    # 3. the invariant, and the three refutations
    it, w = 3000, [1, 4]
    off = None
    for i in range(it):
        if not hasodd(w):
            off = i
            break
        w = nv(w)
    print('#20 "contains an odd" holds for %d laps of nv from a0 = [1;4]: %s'
          % (it, 'OK' if off is None else 'FAILS at lap %d' % off))
    if off is not None:
        bad.append('invariant fails on the orbit')

    print('#20 ...but it is NOT preserved on arbitrary words, and that is'
          ' the open point:')
    for u in ([5, 1], [3, 1], [1, 1, 2, 3, 1]):
        chain = [list(u)]
        for _ in range(2):
            chain.append(nv(chain[-1]))
        print('   %-14s -> %-14s -> %-14s   odd? %s'
              % (chain[0], chain[1], chain[2], hasodd(chain[2])))

    print('#20 nv: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
