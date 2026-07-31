#!/usr/bin/env python3
"""UNTRUSTED: decode anchor words with FIBONACCI digit weights.

Companion to `radix_clock.py`.  That tool says WHAT BASE a machine counts in
without needing an anchor; this one takes the answer "phi" and finds the
anchor, by scoring each candidate family by its longest run of CONSECUTIVE
VALUES under weights

    F(a, b) = a, b, a+b, a+2b, ...        (low digit nearest the head)

instead of 1, 2, 4, 8.  Everything else -- the anchor space (state, head
symbol, which side carries the word, how many cells sit on the other side)
and the consecutive-run score -- is what every scan in `tools/counters`
already does.  The ONLY change is the weight ladder.

WHY IT MATTERS (2026-07-31).  The eleven surviving three-state core rows
(docs/CORE_3STATE.md) had been read for four waves as binary counters whose
anchor is visited at a sparse self-similar set of values --

    1 | 3 | 6,7 | 12,13,15 | 24,25,27,30,31 | ...

-- and the open question was "WHERE is the anchor that sees every
increment?".  There was nothing wrong with the anchor.  Those very words,
weighed 1,1,2,3,5,8,... instead of 1,2,4,8,16, decode to

    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, ...

with ZERO consecutive-value failures over 57,300 transitions.  All eleven
rows read this way, ten under F(1,1) and one under F(1,2), each at an
ordinary flat anchor.  The sparse set was a base-2 misreading, nothing more.

Control: the ladder list includes plain base 2, and the one BASE-2 row in
this population -- `1RB---_1RC1LB_0LB1RD_0RA0RC`, boarded as a binary counter
in `NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.v` -- scores **run = 4 of 4000** here
against the eleven's 4000 of 4000.  So a full-cap score is evidence about the
machine, not an artefact of having offered more ladders.

Untrusted like everything under tools/: it proposes an anchor and an
encoding, and the Coq kernel re-checks every certificate built from one.
"""
import argparse
from collections import defaultdict

from nestscan import run


def ladder(a, b, n=64):
    W = [a, b]
    while len(W) < n:
        W.append(W[-1] + W[-2])
    return W


LADDERS = [('F(1,1)', ladder(1, 1)), ('F(1,2)', ladder(1, 2)),
           ('F(1,3)', ladder(1, 3)), ('F(2,3)', ladder(2, 3)),
           ('base2', [2 ** i for i in range(64)])]


def value(word, W, off):
    if len(word) + off > len(W):
        return None
    return sum(d * W[i + off] for i, d in enumerate(word))


def longest_consec(vals):
    best = cur = 0
    for i, v in enumerate(vals):
        if v is None:
            cur = 0
            continue
        cur = cur + 1 if (cur and vals[i - 1] is not None
                          and v == vals[i - 1] + 1) else 1
        best = max(best, cur)
    return best


def scan(code, T=200000, cap=4000, tmax=3, minw=20):
    fams = defaultdict(list)
    for (q, l, h, r) in run(code, T):
        for t in range(tmax + 1):
            if len(r) == t:
                fams[(q, h, 'L', t)].append(l)
            if len(l) == t:
                fams[(q, h, 'R', t)].append(r)
    best = None
    for key, ws in fams.items():
        ws = ws[:cap]
        if len(ws) < minw:
            continue
        for name, W in LADDERS:
            for off in (0, 1, 2):
                vs = [value(w, W, off) for w in ws]
                n = longest_consec(vs)
                if best is None or n > best[0]:
                    best = (n, len(ws), key, name, off, vs[:10])
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows', help='file of machine codes, one per line')
    ap.add_argument('--steps', type=int, default=200000)
    a = ap.parse_args()
    for code in [l.strip() for l in open(a.rows) if l.strip()]:
        b = scan(code, T=a.steps)
        if b is None:
            print("%-32s -- no anchor family" % code)
            continue
        n, tot, (q, h, side, t), name, off, first = b
        print("%-32s run=%-5d of %-5d  St%s h=S%d word=%s |other|=%d  "
              "%s off=%d\n%34sfirst=%s"
              % (code, n, tot, q, h, side, t, name, off, '', first))


if __name__ == '__main__':
    main()
