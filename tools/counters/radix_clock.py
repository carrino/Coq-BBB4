#!/usr/bin/env python3
"""UNTRUSTED: read a counter's RADIX off its per-cell TOGGLE SPECTRUM.

Every other radix measurement in this tree (`radix_infer.py`,
`alphabet_infer.py`, `digitwidth.py`) has to find an anchor first, then a
word family, then a digit alphabet, and only then can it say what base the
machine counts in.  Each of those steps can fail on a machine that is
perfectly regular, and when one does the row is written down as "no anchor"
and the radix is never learned.

This measures the radix with none of that.  Count, for each tape cell, how
many writes actually CHANGED it.  For a positional counter cell c is a digit
of weight ~r^(c/d), so it changes ~V / r^(c/d) times: the ratio between the
toggle counts of cells [d] apart IS the radix [r], and it needs no anchor, no
word and no alphabet.

Calibrated against machines whose radix is already a theorem here:

    1RB---_0LC1RD_0LB1RD_1LB0RD   base 2   (Counters/KpWallAlt.v)      spread 0.00
    1RB---_1RC1LB_0LB1RD_0RA0RC   base 2   (NLAP_1RB____1RC1LB_...)    stride 2
    1RB---_0LB1RC_0RD0RC_1LB1LD   base 3   (Counters/Ter3Wall.v)       spread 0.00

and the reading it gives on the ELEVEN surviving three-state core rows
(docs/CORE_3STATE.md) is that they are **not an integer base at all**:

    ratio = 1.6180 = phi, spread 0.00, on all eleven,

with the raw toggle counts satisfying F(n) = F(n-1) + F(n-2) exactly.  That
is the signature of a FIBONACCI / ZECKENDORF counter -- digit weights
1, 2, 3, 5, 8, 13, ... rather than 1, 2, 4, 8 -- which is why every alphabet
in theories/Counters (all base 2, plus Ter3Wall's base 3) misses them, and
why their anchor words decode to a sparse self-similar value set under any
binary reading.  Independent cross-check: at t = 2*10^5 those rows have a
23-cell tape and ~4.7*10^4 low-digit toggles; phi^23 ~ 6.4*10^4 (right
order), 2^23 ~ 8.4*10^6 (wrong by two orders).

The estimator is the MEDIAN of the adjacent ratios over cells with at least
500 toggles, and the printed spread is max - min over those ratios: a spread
near 0 means every digit agrees, a large spread means the ladder ran off the
digits (the busiest-cell walk crossed a wall) and the number should not be
trusted.
"""
import argparse
from collections import defaultdict

LAB = "ABCD"
PHI = (1 + 5 ** 0.5) / 2


def parse(code):
    tm = {}
    for i, blk in enumerate(code.split("_")):
        q = LAB[i]
        for s in (0, 1):
            t = blk[3 * s:3 * s + 3]
            tm[(q, s)] = None if t == "---" else (int(t[0]), t[1], t[2])
    return tm


def toggles(code, T):
    """cell -> number of writes that changed it."""
    tm = parse(code)
    tape = defaultdict(int)
    pos = 0
    q = 'A'
    tog = defaultdict(int)
    for _ in range(T):
        tr = tm[(q, tape[pos])]
        if tr is None:
            break
        w, d, n = tr
        if w != tape[pos]:
            tog[pos] += 1
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = n
    return tog


def spectrum(tog, d):
    """Toggle counts down the digit ladder at stride [d], busiest cell first.
    Walks both ways from the busiest cell and keeps the DECREASING arm --
    the counter grows one way, and the other way is the wall."""
    if not tog:
        return []
    c0 = max(tog, key=lambda c: tog[c])
    for step in (d, -d):
        arm, c = [], c0
        while c in tog and tog[c] > 40:
            arm.append(tog[c])
            c += step
        if len(arm) >= 4 and arm[1] < arm[0]:
            return arm
    return []


def read_radix(code, T=400000, floor=500, keep=8):
    out = []
    for d in (1, 2, 3):
        sp = [c for c in spectrum(toggles(code, T), d) if c >= floor][:keep]
        if len(sp) < 4:
            continue
        rs = sorted(sp[i] / sp[i + 1] for i in range(len(sp) - 1))
        n = len(rs)
        med = rs[n // 2] if n % 2 else (rs[n // 2 - 1] + rs[n // 2]) / 2
        out.append((rs[-1] - rs[0], d, med, sp))
    if not out:
        return None
    out.sort()
    spread, d, med, sp = out[0]
    fib = all(abs(sp[i] - sp[i + 1] - sp[i + 2]) <= 2
              for i in range(len(sp) - 2))
    if abs(med - PHI) < 0.01:
        name = 'phi (Fibonacci/Zeckendorf)'
    elif abs(med - round(med)) < 0.03:
        name = 'base %d' % round(med)
    else:
        name = '?'
    return d, med, spread, name, fib, sp


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows', help='file of machine codes, one per line')
    ap.add_argument('--steps', type=int, default=400000)
    a = ap.parse_args()
    for code in [l.strip() for l in open(a.rows) if l.strip()]:
        r = read_radix(code, T=a.steps)
        if r is None:
            print("%-32s -- no toggle ladder" % code)
            continue
        d, med, spread, name, fib, sp = r
        print("%-32s stride=%d  ratio=%.4f (spread %.2f) -> %-26s %s\n"
              "%34scounts=%s"
              % (code, d, med, spread, name,
                 'F(n)=F(n-1)+F(n-2) holds' if fib else '', '', sp))


if __name__ == '__main__':
    main()
