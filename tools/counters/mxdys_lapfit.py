#!/usr/bin/env python3
"""UNTRUSTED: validate an anchor family DECODED FROM mxdys' `Inductive` rule
against the raw simulator, and report the three LapGlue premises.

`Inductive` hands over a symbolic config family (see
docs/MXDYS_INDUCTIVE_RESIDUE.md) but proves only non-halting.  This probe turns
that family into the objects `LapGlue.glue_neverqh` needs and checks each one
against a plain step-by-step simulator -- the differential validation the tree
requires before any Coq is written:

  Hboot   blank tape reaches Cf(p0), at which step
  Hlap    Cf(m) -->^f(m) Cf(m+1), exactly, over a range of m, with f fitted affine
  Hvis    which transitions fire inside one lap (all 8 => every state recurs)

Default family is `1RB1LB_1LC0RD_0LB1LA_0LA1RA`'s, decoded from

    {0inf >[A] 0inf} -->lb[n] {1 (01)^(2n+21) (0 1^4)^(n+13) 0inf <[C] (0)^1 1 0inf}

into bbchallenge orientation as

    Cf m = (StC, ([S1], S0, [S1] ++ rep [S0;S1] (2m-5) ++ rep [S0;S1;S1;S1;S1] m))

    python3 tools/counters/mxdys_lapfit.py                 # the full report
    python3 tools/counters/mxdys_lapfit.py --split         # + the two-pass split
"""
import argparse
from collections import defaultdict

SPEC = '1RB1LB_1LC0RD_0LB1LA_0LA1RA'
ST = 'ABCD'


def parse(spec):
    tm = {}
    for qi, g in enumerate(spec.split('_')):
        for si in range(2):
            t = g[3 * si:3 * si + 3]
            tm[(qi, si)] = None if t == '---' else (
                int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return tm


def shape(word_right, state=2, left=(1,)):
    """Build a config: head at 0, `left` written outward from the head."""
    tp = defaultdict(int)
    for i, s in enumerate(left):
        tp[-1 - i] = s
    for i, ch in enumerate(word_right):
        tp[i + 1] = int(ch)
    return state, tp, 0


def Cf(m):
    return shape('1' + '01' * (2 * m - 5) + '01111' * m)


def G(m):
    """The mid-lap rest: the (01) block has grown to 2m-2, the (01111) block
    has not moved yet."""
    return shape('1' + '01' * (2 * m - 2) + '01111' * m)


def same(q, tp, pos, tgt):
    q2, tp2, pos2 = tgt
    if q != q2:
        return False
    return all(tp[k] == tp2[k - pos + pos2] for k in set(tp) | set(tp2))


def run_until(tm, start, targets, cap):
    """Step from `start` until one of `targets` (list of (name, cfg)) matches.
    Returns (name, steps, fired-transition set) or None."""
    q, tp, pos = start
    tp = defaultdict(int, tp)
    fired = set()
    for t in range(1, cap + 1):
        tr = tm[(q, tp[pos])]
        if tr is None:
            return None
        fired.add((q, tp[pos]))
        w, d, nq = tr
        tp[pos] = w
        pos += d
        q = nq
        for name, cfg in targets:
            if same(q, tp, pos, cfg):
                return name, t, fired
    return None


def affine(points):
    """Fit f(m) = a*m + b through the first two, verify on the rest."""
    (m0, y0), (m1, y1) = points[0], points[1]
    a = (y1 - y0) // (m1 - m0)
    b = y0 - a * m0
    ok = all(a * m + b == y for m, y in points)
    return a, b, ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec', default=SPEC)
    ap.add_argument('--lo', type=int, default=3)
    ap.add_argument('--hi', type=int, default=25)
    ap.add_argument('--split', action='store_true')
    a = ap.parse_args()
    tm = parse(a.spec)
    print('spec %s' % a.spec)

    # Hboot -----------------------------------------------------------------
    blank = (0, defaultdict(int), 0)
    r = run_until(tm, blank, [('Cf%d' % a.lo, Cf(a.lo))], 200000)
    print('Hboot : blank tape -> Cf(%d) in %s steps'
          % (a.lo, r[1] if r else 'NOT FOUND'))

    # Hlap ------------------------------------------------------------------
    pts, allfired = [], None
    for m in range(a.lo, a.hi + 1):
        r = run_until(tm, Cf(m), [('next', Cf(m + 1))], 10 ** 6)
        if not r:
            print('Hlap  : NO LAP from Cf(%d)' % m)
            return
        pts.append((m, r[1]))
        allfired = r[2] if allfired is None else (allfired & r[2])
    coef_a, coef_b, ok = affine(pts)
    print('Hlap  : Cf(m) -->^(%d*m %+d) Cf(m+1)   exact for m = %d..%d : %s'
          % (coef_a, coef_b, a.lo, a.hi, ok))

    # Hvis ------------------------------------------------------------------
    fs = sorted('%s%d' % (ST[q], s) for q, s in allfired)
    states = sorted({ST[q] for q, _ in allfired})
    print('Hvis  : transitions fired in EVERY lap: %s  => states %s'
          % (' '.join(fs), ''.join(states)))
    if len(states) == 4:
        print('        all four states recur -- Hvis is free')

    # the two-pass split ----------------------------------------------------
    if a.split:
        p1, p2 = [], []
        for m in range(a.lo, min(a.hi, 14) + 1):
            r1 = run_until(tm, Cf(m), [('G', G(m))], 10 ** 6)
            r2 = run_until(tm, G(m), [('next', Cf(m + 1))], 10 ** 6)
            if not (r1 and r2):
                print('split : no G(%d) rest' % m)
                return
            p1.append((m, r1[1]))
            p2.append((m, r2[1]))
        for tag, pts2 in (('Cf(m)->G(m)', p1), ('G(m)->Cf(m+1)', p2)):
            ca, cb, ok2 = affine(pts2)
            print('split : %-14s  %d*m %+d   exact: %s' % (tag, ca, cb, ok2))


if __name__ == '__main__':
    main()
