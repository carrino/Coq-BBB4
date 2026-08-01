#!/usr/bin/env python3
"""UNTRUSTED (tools/): the SOLID-BLOCK wall anchor, and the two core rows
that have it.

LADDER_PLAN 4w, from John's reading of the two rows.  Both

    1RB1LA_0LA0LC_1LC1RD_0RB0RD      (+2 shadows)
    1RB0RB_0LC1RD_1LC1LA_0LA1RB      (+1 shadow)

have the SAME one-parameter anchor family, and it is the simplest shape in
the residue:

    Cf w = (StA, ([], S0, rep [S1] w))

-- the head on a blank, nothing to its left, and a solid block of `w` ones
to its right.  The block grows by exactly ONE cell per lap on both rows, and
each lap runs an inner counter over the block.  What differs is only the
inner counter, and it is visible in the lap law:

    1RB1LA_0LA0LC_1LC1RD_0RB0RD    lap(w) = 2^(w+3) - (2w + 5)     BINARY
    1RB0RB_0LC1RD_1LC1LA_0LA1RB    lap(w) = lap(w-1)+lap(w-2)+3    FIBONACCI

John reads the first as "a counter where moving the carry bit x spots over
takes x bounces" -- which is why the arm cost has a constant SECOND
difference (4p) and why no widening of the ladder's `ARM_GRID` reaches it:
the carry is an inner LOOP, not an affine arm.  He reads the second as
"counts down from 1111 whenever the left wall moves over; the bits are
inverted, lsb on the right; the left wall moves over 1 on each overflow",
and the Fibonacci lap recurrence is that countdown's length.

**Why this matters**: `docs/CORE_3STATE.md` section 3 recorded of the second
row that "its once-per-increment anchor is not located", and LADDER_PLAN 4s
measured that `digit_words(rules)` names NOTHING at any anchor on it.  Both
are true of the DIGIT-family search, and both stop being the question here:
the anchor is not a digit family at all, it is a bare run.

    python3 tools/counters/wallblock.py [--steps N]
"""
import argparse
from collections import defaultdict

ROWS = ["1RB1LA_0LA0LC_1LC1RD_0RB0RD", "1RB0RB_0LC1RD_1LC1LA_0LA1RB"]


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def trim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def step(tab, c):
    st, l, h, r = c
    e = tab[(st, h)]
    if e is None:
        return None
    w, d, ns = e
    if d == +1:
        return (ns, [w] + list(l), r[0] if r else 0, list(r[1:]))
    return (ns, list(l[1:]), l[0] if l else 0, [w] + list(r))


def hits(spec, T):
    """the steps at which the machine is at [Cf w], per width."""
    tab = parse(spec)
    c = (0, [], 0, [])
    out = {}
    for n in range(T):
        st, l, h, r = c
        if st == 0 and h == 0 and not trim(l):
            rr = trim(r)
            if rr and all(x == 1 for x in rr) and len(rr) not in out:
                out[len(rr)] = n
        c = step(tab, c)
        if c is None:
            break
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=400000)
    a = ap.parse_args()
    for spec in ROWS:
        h = hits(spec, a.steps)
        ks = sorted(h)[:12]
        laps = [h[ks[i + 1]] - h[ks[i]] for i in range(len(ks) - 1)]
        print(spec)
        print("  Cf w = (StA, ([], S0, rep [S1] w))")
        print("  boot t  " + ", ".join("w=%d:%d" % (w, h[w]) for w in ks[:6]))
        print("  laps    " + ", ".join(map(str, laps)))
        pow2 = all(laps[i] == 2 ** (ks[i] + 3) - (2 * ks[i] + 5)
                   for i in range(len(laps)))
        fib = all(laps[i] == laps[i - 1] + laps[i - 2] + 3
                  for i in range(2, len(laps)))
        print("  lap = 2^(w+3) - (2w+5)          %s" % pow2)
        print("  lap = lap(w-1) + lap(w-2) + 3   %s" % fib)


if __name__ == '__main__':
    main()
