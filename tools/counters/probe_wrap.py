#!/usr/bin/env python3
"""Tape probe for the two 1RB--- wrap holdouts (UNTRUSTED).

    W15 = 1RB---_1RC0RB_0LC0RD_1LD1LB      (the "bouncer" read)
    W07 = 1RB---_1LC0LB_0RC0LD_1RD1RB      (its core is W15's core, mirrored)

Both quasihalt trivially: nothing targets StA, so A is visited once and is
quiet from step 0.  What is NOT proven is that B, C, D are each visited
INFINITELY often -- without that there is no [QHBound] and so no [boarded].
So the only thing this probe needs to expose is the recurrence structure of
the {B,C,D} core, from the config A hands off (a single 1 at position 0,
head at position 1, state B).

Prints a step trace as cconf = (state, (left-nearest-first, head, right)),
which is the same shape the Coq [csteps] lemmas take, so runs read off
directly.

Usage:  probe_wrap.py [MACHINE] [STEPS]
"""
import sys

LAB = "ABCD"
StA, StB, StC, StD = 0, 1, 2, 3

MACHINES = {
    'W15': "1RB---_1RC0RB_0LC0RD_1LD1LB",
    'W07': "1RB---_1LC0LB_0RC0LD_1RD1RB",
}


def parse(spec):
    """'1RB---_1RC0RB_...' -> {(state,sym): (write, dir, next)}; None = halt."""
    tm = {}
    for q, blk in enumerate(spec.split('_')):
        for s in (0, 1):
            t = blk[3 * s:3 * s + 3]
            if t == '---':
                tm[(q, s)] = None
            else:
                tm[(q, s)] = (int(t[0]), +1 if t[1] == 'R' else -1,
                              LAB.index(t[2]))
    return tm


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def cstep(tm, c):
    st, (l, h, r) = c
    t = tm[(st, h)]
    if t is None:
        return None
    w, d, ns = t
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r)))
    return (ns, (ctl(l), chd(l), [w] + r))


def show(c):
    st, (l, h, r) = c
    ls = ''.join(str(x) for x in reversed(l))
    rs = ''.join(str(x) for x in r)
    return "%s  %s[%d]%s" % (LAB[st], ls, h, rs)


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'W15'
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    spec = MACHINES.get(name, name)
    tm = parse(spec)
    print("%s = %s" % (name, spec))
    c = (StA, ([], 0, []))
    for n in range(steps + 1):
        print("%5d  %s" % (n, show(c)))
        c = cstep(tm, c)
        if c is None:
            print("HALT at %d" % n)
            return


if __name__ == '__main__':
    main()
