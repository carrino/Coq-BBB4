#!/usr/bin/env python3
"""UNTRUSTED search for [Checkers/ReachStI.v] certificates.

For a machine, a goal state [qgoal] and an allowed state set (the invariant
"the state is in [allowed]"), look for the measure

    mu (q,(l,h,r)) = B * ones l + C * ones r + rk (q, chd l, h, chd r)

that strictly DROPS on every step which does not land on [qgoal].  [mu] is a
nat, so a strict drop bounds the goal-avoiding run -- which is [ReachStI].

The drop is read straight off [CTape.ctape_move], exactly as [drop_ok] does:

    DR  (l,h,r) -> (w::l, chd r, ctl r)    ones l += w    ones r -= chd r
    DL  (l,h,r) -> (ctl l, chd l, w::r)    ones r += w    ones l -= chd l

so with [b = chd r], [a = chd l] and [x] the cell freshly exposed behind the
one being crossed (the only unknown -- quantified over),

    DR:  rk (q', w, b, x) - rk (q,a,h,b)  <=  -1 - B*w + C*b
    DL:  rk (q', x, a, w) - rk (q,a,h,b)  <=  -1 - C*w + B*a

For fixed (B,C) that is a difference-constraint system on [rk]; Bellman-Ford
decides it and returns the pointwise-least solution, shifted to be a nat.

Nothing here carries proof weight.  A wrong constant makes [drop_ok]
evaluate to [false]; it cannot make anything provable.

Usage: cert_search.py <machine> [<qgoal>] [<allowed>]
"""
import sys
from itertools import product

LAB = 'ABCD'


def parse(spec):
    tab = {}
    for qi, part in enumerate(spec.split('_')):
        for s in (0, 1):
            f = part[3 * s:3 * s + 3]
            tab[(qi, s)] = (None if f in ('---', '1RZ')
                            else (int(f[0]), 1 if f[1] == 'R' else -1, LAB.index(f[2])))
    return tab


def allowed_set(tab):
    """The largest state set that is TOTAL and CLOSED under the table --
    exactly what [inv_ok] checks."""
    a = [q for q in range(4) if all(tab[(q, s)] is not None for s in (0, 1))]
    changed = True
    while changed:
        changed = False
        for q in list(a):
            if any(tab[(q, s)][2] not in a for s in (0, 1)):
                a.remove(q)
                changed = True
    return a


def invariant_ok(tab, allowed):
    for q in allowed:
        for s in (0, 1):
            tr = tab[(q, s)]
            if tr is None or tr[2] not in allowed:
                return False
    return True


def nodes(allowed):
    return [(q, a, h, b) for q in allowed
            for a in (0, 1) for h in (0, 1) for b in (0, 1)]


def raw_edges(tab, qgoal, allowed):
    """(node, node', d_ones_l, d_ones_r) for every goal-avoiding step."""
    out = []
    for (q, a, h, b) in nodes(allowed):
        if q == qgoal:
            continue
        w, d, q2 = tab[(q, h)]
        if q2 == qgoal:
            continue
        for x in (0, 1):
            if d > 0:
                out.append(((q, a, h, b), (q2, w, b, x), w, -b))
            else:
                out.append(((q, a, h, b), (q2, x, a, w), -a, w))
    return out


def feasible(tab, qgoal, allowed, B, C):
    ns = nodes(allowed)
    cons = [(u, v, -1 - B * dl - C * dr)
            for (u, v, dl, dr) in raw_edges(tab, qgoal, allowed)]
    rk = {n: 0 for n in ns}
    for _ in range(len(ns) + 1):
        changed = False
        for (u, v, lim) in cons:
            if rk[v] > rk[u] + lim:
                rk[v] = rk[u] + lim
                changed = True
        if not changed:
            break
    else:
        return None                        # negative cycle: infeasible
    if any(rk[v] > rk[u] + lim for (u, v, lim) in cons):
        return None
    lo = min(rk.values())
    return {n: rk[n] - lo for n in rk}


def search(spec, qgoal, allowed, maxBC=4):
    tab = parse(spec)
    if not invariant_ok(tab, allowed):
        return None
    for B, C in sorted(product(range(maxBC + 1), repeat=2), key=sum):
        rk = feasible(tab, qgoal, allowed, B, C)
        if rk is not None:
            return B, C, rk
    return None


def main():
    spec = sys.argv[1]
    tab = parse(spec)
    allowed = ([LAB.index(c) for c in sys.argv[3]] if len(sys.argv) > 3
               else allowed_set(tab))
    goals = [LAB.index(sys.argv[2])] if len(sys.argv) > 2 else allowed
    for qg in goals:
        r = search(spec, qg, allowed)
        print('%s goal=%s allowed=%s %s' % (
            spec, LAB[qg], ''.join(LAB[a] for a in allowed),
            'B=%d C=%d' % (r[0], r[1]) if r else 'NONE'))


if __name__ == '__main__':
    main()
