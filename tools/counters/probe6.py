#!/usr/bin/env python3
"""Step-level probe for wave machine #6 (1RB0LB_0LB0RC_1LD1RC_1LA1RB).

Same contract as probe27.py: mirrors CTape.cstep EXACTLY (cconf =
(state,(left,head,right)), left nearest-first, blanks materialised as S0
at the edges), so every window printed here transcribes verbatim into a
Coq [wsteps]/[csteps] reflexivity lemma.

#6 is edge C, side R, poff 1, and shares the #27 abstract orbit
(nextf 1 / WInv 1, boot [1;1;2;4]) -- see tools/counters/trace_wave.py.
Its cross cycle is 4 steps (vs #27's 2), which is the whole delta.

Usage:  probe6.py [front...]        e.g. probe6.py 4 2 1
        probe6.py --units           dump the gadget units
"""
import sys

# 1RB0LB_0LB0RC_1LD1RC_1LA1RB   states A,B,C,D = 0..3
TM = {
    (0, 0): (1, +1, 1), (0, 1): (0, -1, 1),   # A0=1RB A1=0LB
    (1, 0): (0, -1, 1), (1, 1): (0, +1, 2),   # B0=0LB B1=0RC
    (2, 0): (1, -1, 3), (2, 1): (1, +1, 2),   # C0=1LD C1=1RC
    (3, 0): (1, -1, 0), (3, 1): (1, +1, 1),   # D0=1LA D1=1RB
}
LAB = "ABCD"
EDGE = 2      # StC
POFF = 1


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def cstep(c):
    st, (l, h, r) = c
    w, d, ns = TM[(st, h)]
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r)))
    return (ns, (ctl(l), chd(l), [w] + r))


def csteps(c, n):
    for _ in range(n):
        c = cstep(c)
    return c


def show(c):
    st, (l, h, r) = c
    ls = ''.join(str(x) for x in reversed(l))
    rs = ''.join(str(x) for x in r)
    return "%s [%s](%d)[%s]" % (LAB[st], ls, h, rs)


def wbody(front):
    if not front:
        return [1]
    b, r = front[0], front[1:]
    return [1] * b + [0] + wbody(r)


def carry(po, blocks):
    if not blocks:
        return [] if po else [1]
    b, r = blocks[0], blocks[1:]
    if po:
        return [b + 1] + r
    return [b] + carry(b % 2 == 1, r)


def nextf(poff, front):
    if not front:
        return []
    b0, r = front[0], front[1:]
    return [b0 + 1] + carry((b0 + poff) % 2 == 1, r)


def Cf6(front):
    """(StC, (wbody front, S0, [])) -- head one cell right of the frontier."""
    return (EDGE, (wbody(front), 0, []))


def run_to_event(front, verbose=True):
    c = Cf6(front)
    tgt = Cf6(nextf(POFF, front))
    hist = [c]
    for steps in range(1, 200001):
        c = cstep(c)
        hist.append(c)
        st, (l, h, r) = c
        if st == EDGE and h == 0 and r == [] and l and l[0] == 1:
            if l == tgt[1][0]:
                if verbose:
                    print("  %s -> %s in %d steps" %
                          (front, nextf(POFF, front), steps))
                return steps, hist, True
    if verbose:
        print("  %s: NO EVENT" % front)
    return None, hist, False


def trace(front, limit=400):
    print("=== front=%s  nextf=%s ===" % (front, nextf(POFF, front)))
    steps, hist, ok = run_to_event(front)
    print("  match=%s" % ok)
    for i, c in enumerate(hist[:limit]):
        print("   %3d: %s" % (i, show(c)))


def units():
    """Dump the candidate gadget windows, as Coq-ready wsteps facts."""
    print("-- cross cycle: state C on a run of ones, head S1, leftward? --")
    for k in range(0, 5):
        c = (EDGE, ([1] * k + [0], 0, []))
        print("   C ([1^%d;0],0,[])  ->" % k, end="")
        cur = c
        for n in range(1, 13):
            cur = cstep(cur)
            print("  %d:%s" % (n, show(cur)), end="")
        print()
    print()
    print("-- 4-step iterates from (C,([1],1,R)) --")
    for k in range(1, 6):
        c = (EDGE, ([1] * k, 1, []))
        print("   k=%d start %s" % (k, show(c)))
        cur = c
        for n in range(1, 4 * k + 6):
            cur = cstep(cur)
            print("        %2d: %s" % (n, show(cur)))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if '--units' in sys.argv:
        units()
        return
    front = [int(x) for x in args] or [4, 2, 1]
    trace(front)


if __name__ == '__main__':
    main()
