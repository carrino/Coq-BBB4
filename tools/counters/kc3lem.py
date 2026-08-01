#!/usr/bin/env python3
"""UNTRUSTED (tools/): state the KCOPY3 row's lap law AGAINST THE PROBE, in
single cells, over ALL instantiations of the unknown context.

Same discipline as `bin3lem.py` (`docs/LADDER_PLAN.md` §4z): every rule is run
on a tape whose cells outside the rule's own statement are UNKNOWN, and the
run ABORTS the moment the head reads one.  A rule that survives is a rule
whose Coq statement cannot be too weak in the context, which is the failure
`srun`'s `XL`/`XR` opacity is there to prevent.

The anchor of `1RB1RC_1LA1RA_0RC1LD_1LB0LD` is

    Cc p = (StC, (Wk p, S1, []))          -- left list is HEAD-OUTWARD

and `cview` splits it into THREE branches, not two.  `Wk` is the packed
numeral of `kc3lap.py`: three cells a digit except the top digit, which is
one, under a three-cell marker.

    INT  cview p = (j, Some q0), q0 <> 1
         (StC, (rep [S1;S1;S1] j ++ [S0;S0;S0] ++ X, S1, []))
      -> (StC, (rep [S0;S0;S0] j ++ [S1;S1;S1] ++ X, S1, []))    6j+6

    FRT  cview p = (j, Some 1)            -- carry lands ON the packed digit
         (StC, (rep [S1;S1;S1] j ++ [S0;S1;S1;S1], S1, []))
      -> (StC, (rep [S0;S0;S0] j ++ [S1;S1;S1;S1], S1, []))      6j+4

    OVF  cview p = (S j, None)
         (StC, (rep [S1;S1;S1] j ++ [S1], S1, []))
      -> (StC, (rep [S0;S0;S0] j ++ [S0;S1;S1;S1], S1, []))      6(S j)+2

    python3 tools/counters/kc3lem.py [--jmax N]
"""
import argparse

SPEC = "1RB1RC_1LA1RA_0RC1LD_1LB0LD"
LAB = "ABCD"
U = '?'


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


TAB = parse(SPEC)


class Unknown(Exception):
    pass


def probe(st, left, head, right, nsteps):
    """Run `nsteps` from (st, (left, head, right)); every cell outside the
    three lists is UNKNOWN and reading one aborts.  `left` is head-outward."""
    cells = {0: head}
    for i, c in enumerate(left):
        cells[-1 - i] = c
    for i, c in enumerate(right):
        cells[1 + i] = c
    lo, hi = -len(left), len(right)
    pos = 0
    for _ in range(nsteps):
        if pos < lo or pos > hi:
            raise Unknown("head read an UNKNOWN cell at %d" % pos)
        s = cells[pos]
        if s == U:
            raise Unknown("head read an UNKNOWN cell at %d" % pos)
        e = TAB[(st, s)]
        if e is None:
            raise Unknown("halt")
        w, d, st = e
        cells[pos] = w
        pos += d
    if pos < lo or pos > hi:
        raise Unknown("finished on an UNKNOWN cell")
    L, R = [], []
    i = pos - 1
    while i >= lo:
        L.append(cells[i]); i -= 1
    i = pos + 1
    while i <= hi:
        R.append(cells[i]); i += 1
    while L and L[-1] == 0:
        L.pop()
    while R and R[-1] == 0:
        R.pop()
    return st, L, cells[pos], R


def rep(u, k):
    return list(u) * k


def check(name, j, left, cost, exp_left, ctx):
    """`ctx` is the opaque tail appended past the numeral's top, as UNKNOWNs."""
    try:
        st, L, h, R = probe(2, left + [U] * ctx, 1, [], cost)
    except Unknown as e:
        return "%-4s j=%-2d  ABORT (%s)" % (name, j, e)
    okL = L[:len(exp_left)] == exp_left and all(c == U for c in L[len(exp_left):])
    ok = st == 2 and h == 1 and R == [] and okL and len(L) == len(exp_left) + ctx
    return "%-4s j=%-2d  cost %-4d  %s  end=(St%s, %s, S%s, %s)" % (
        name, j, cost, "OK " if ok else "MISMATCH",
        LAB[st], ''.join(map(str, L)), h, ''.join(map(str, R)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--jmax', type=int, default=6)
    ap.add_argument('--ctx', type=int, default=4,
                    help='unknown cells past the top of the stated region')
    a = ap.parse_args()
    print("machine %s   anchor (StC, (Wk p, S1, []))" % SPEC)
    print("-- INT: cview p = (j, Some q0), q0 <> 1;  the tail X is UNKNOWN")
    for j in range(a.jmax + 1):
        print("  " + check("INT", j,
                           rep([1, 1, 1], j) + [0, 0, 0], 6 * j + 6,
                           rep([0, 0, 0], j) + [1, 1, 1], a.ctx))
    print("-- FRT: cview p = (j, Some 1);  the numeral ENDS, tail is UNKNOWN")
    for j in range(a.jmax + 1):
        print("  " + check("FRT", j,
                           rep([1, 1, 1], j) + [0, 1, 1, 1], 6 * j + 4,
                           rep([0, 0, 0], j) + [1, 1, 1, 1], a.ctx))
    print("-- OVF: cview p = (S j, None);  the numeral ENDS, tail is UNKNOWN")
    for j in range(a.jmax + 1):
        print("  " + check("OVF", j,
                           rep([1, 1, 1], j) + [1], 6 * (j + 1) + 2,
                           rep([0, 0, 0], j) + [0, 1, 1, 1], a.ctx))


if __name__ == '__main__':
    main()
