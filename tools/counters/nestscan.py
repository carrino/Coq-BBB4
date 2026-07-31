#!/usr/bin/env python3
"""UNTRUSTED: find a counter anchor by the LOCAL increment structure of
consecutive anchor words, instead of by decoding them to consecutive integers.

WHY THIS EXISTS.  Every other anchor search in this tree -- `anchor_scan`,
`anchor_snaps_all`, `anchor_snaps_far_all`, `radix_infer`, `carry_anchor`, and
`emit_lapcert.anchors` -- scores a candidate family by the length of its
longest run of CONSECUTIVE VALUES.  That is the right score for a counter that
counts forever at one width.  It is the WRONG score for a NESTED counter --
fixed width inside an epoch, widening between epochs -- because such a machine
only supplies consecutive values INSIDE one epoch, and the early epochs are
short.  `1RB---_1RC1LB_0LB1RD_0RA0RC` is exactly that: its anchor value runs
2^(2i) .. 2^(2i+1) - 1 and then JUMPS to 2^(2i+2), so at 400k steps the best
consecutive run those searches can see is a few dozen, buried under noise.
It was read as "no anchor / no overflow phase" for four waves
(`residue_map.tsv`), and it is a plain binary counter.

WHAT IS SCORED HERE INSTEAD.  The [Alph] increment is a purely LOCAL fact
about a PAIR of adjacent anchor words:

    w  = pre ++ B^j ++ A ++ tail          w' = pre ++ A^j ++ B ++ tail

so (A, B) can be read off the pair itself, with no notion of "the value".
This scan reads every candidate (A, B, |pre|) out of every adjacent pair,
votes, and then reports the longest CONSECUTIVE stretch of pairs that admit
the winner -- plus the word lengths at each break, which are the epoch
boundaries and tell you the outer growth law at a glance.

An anchor is (state, head symbol, which side carries the word, how many cells
sit on the other side) -- i.e. the head at a fixed offset from a tape end,
the same anchor space the other scans use.  Only the SCORE is different.

Calibration: on `1RB---_1RC1LB_0LB1RD_0RA0RC` the top three families all
score run=255 with A=01, B=11, among them

    StB h=S0 word=L |other|=0 : run=255 A=01 B=11 pre=1
      breaks at (5, 6->10), (21, 10->14), (85, 14->18), (341, 18->22)

which is the anchor `NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.v` is built on: the
word grows by two digits per epoch and the epochs are 4, 16, 64, 256 laps
long, so the breaks land at 5, 21, 85, 341.  Nothing else in the tree scores
that family above noise.

Measured NEGATIVE (2026-07-31) on all eleven surviving `1RB---` core rows:
best stretch 1 or 2 pairs at every anchor, with the word length growing at
nearly every anchor rather than staying fixed inside an epoch.  So the
"nested counter read at a flat anchor" shape that closes the `StA` row is
NOT what those eleven are; see docs/CORE_3STATE.md section 3.

The reason is upstream of this scan and of every other one: `radix_clock.py`
measures those eleven counting in `phi`, not in 2, and the `(A, B)` increment
fitted here is a fixed-radix increment.  Run `radix_clock.py` FIRST -- it
needs no anchor at all, so it answers on rows where this scan cannot.

Untrusted like everything under tools/: it proposes an anchor, and the Coq
kernel re-checks every certificate built from one.
"""
import argparse
from collections import defaultdict

LAB = "ABCD"


def parse(code):
    tm = {}
    for i, blk in enumerate(code.split("_")):
        q = LAB[i]
        for s in (0, 1):
            t = blk[3 * s:3 * s + 3]
            tm[(q, s)] = None if t == "---" else (int(t[0]), t[1], t[2])
    return tm


def run(code, T):
    """Yield (state, left, head, right), both sides nearest-first with
    trailing blanks stripped -- the same normal form conf() uses elsewhere."""
    tm = parse(code)
    tape = defaultdict(int)
    pos = 0
    q = 'A'
    lo = hi = 0
    for _ in range(T):
        left = [tape[i] for i in range(pos - 1, lo - 1, -1)]
        right = [tape[i] for i in range(pos + 1, hi + 1)]
        while left and left[-1] == 0:
            left.pop()
        while right and right[-1] == 0:
            right.pop()
        yield (q, tuple(left), tape[pos], tuple(right))
        tr = tm[(q, tape[pos])]
        if tr is None:
            return
        w, d, n = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = n
        lo = min(lo, pos)
        hi = max(hi, pos)


def fit_pair(w, wp, dmax=3, pmax=3):
    """Every (A, B, |pre|) with w = pre B^j A tail and wp = pre A^j B tail.

    The prefix is not decoration: an anchor word normally carries the stop
    digit's own marker in front of the carry run, and pinning |pre| = 0 loses
    the family.  The [j = 0] case needs its own arm -- there B does not occur
    in [w] at all, so it has to be read from [w']."""
    out = set()
    if len(w) != len(wp) or not w:
        return out
    ms = 0                                  # longest common suffix: |tail| <= ms
    while ms < len(w) and w[len(w) - 1 - ms] == wp[len(wp) - 1 - ms]:
        ms += 1
    for p in range(min(pmax, len(w)) + 1):
        if w[:p] != wp[:p]:
            break
        for k in range(min(ms, len(w) - p) + 1):
            head, headp = w[p:len(w) - k], wp[p:len(wp) - k]
            if not head:
                continue
            for d in range(1, dmax + 1):
                if len(head) % d:
                    continue
                j = len(head) // d - 1
                if j == 0:
                    A, B = head, headp
                else:
                    B, A = head[:d], head[j * d:]
                if A != B and head == B * j + A and headp == A * j + B:
                    out.add((A, B, p))
    return out


def scan(code, T=200000, cap=400, dmax=3, pmax=3, tmax=3, minw=12):
    fams = defaultdict(list)
    for (q, l, h, r) in run(code, T):
        for t in range(tmax + 1):
            if len(r) == t:
                fams[(q, h, 'L', t)].append(l)
            if len(l) == t:
                fams[(q, h, 'R', t)].append(r)
    out = []
    for key, ws in fams.items():
        ws = ws[:cap]
        if len(ws) < minw:
            continue
        fits = [fit_pair(ws[i], ws[i + 1], dmax, pmax)
                for i in range(len(ws) - 1)]
        votes = defaultdict(int)
        for f in fits:
            for cand in f:
                votes[cand] += 1
        if not votes:
            continue
        (A, B, p), n = max(votes.items(), key=lambda kv: kv[1])
        best = cur = 0
        breaks = []
        for i, f in enumerate(fits):
            if (A, B, p) in f:
                cur += 1
                best = max(best, cur)
            else:
                if cur:
                    breaks.append((i, len(ws[i]), len(ws[i + 1])))
                cur = 0
        out.append((best, n, len(ws), key, A, B, p, breaks[:6]))
    out.sort(reverse=True)
    return out


def _s(t):
    return ''.join(map(str, t)) if t else '.'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows', help='file of machine codes, one per line')
    ap.add_argument('--steps', type=int, default=200000)
    ap.add_argument('--top', type=int, default=4)
    ap.add_argument('--minrun', type=int, default=0,
                    help='only print families whose best stretch reaches this')
    a = ap.parse_args()
    for code in [l.strip() for l in open(a.rows) if l.strip()]:
        res = [r for r in scan(code, T=a.steps) if r[0] >= a.minrun]
        print("=== %s" % code)
        if not res:
            print("    no incrementing anchor family")
        for (best, n, tot, key, A, B, p, breaks) in res[:a.top]:
            q, h, side, t = key
            print("    St%s h=S%d word=%s |other|=%d : run=%-4d fits=%d/%d "
                  "A=%s B=%s pre=%d  breaks(at,|w|,|w'|)=%s"
                  % (q, h, side, t, best, n, tot - 1, _s(A), _s(B), p, breaks))


if __name__ == '__main__':
    main()
