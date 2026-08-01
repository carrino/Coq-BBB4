#!/usr/bin/env python3
"""UNTRUSTED (tools/): state the D0-landmark macro rules of Drozd's sixth row
IN SINGLE CELLS and check them against the probe BEFORE they are proved --
`bin3lem.py` / `kc3lem.py` discipline.

The landmark is the exact `cconf`  (StD, (l, S0, []))  -- measured to have a
LITERALLY EMPTY right list at every visit.  With  l = rep S0 z ++ S1 :: l2
(head-outward) the claimed rules are, in single cells:

  (i)   l2 = S1 :: l3          l' = rep S1 z      ++ S0::S0::l3          2z+4
  (ii)  chd l2 = S0, z >= 1    l' = rep S1 (z-1)  ++ S0::S0::S1::ctl l2  2z+4
  (iii) chd l2 = S0, z  = 0    l' = S0::S0::S1::S1::ctl l2              10

Two checks, both required:

  --orbit   run the real machine and confirm every landmark-to-landmark
            transition is the claimed branch, with the claimed step count;
  --ctx     run each rule on a tape whose cells OUTSIDE the lemma's own
            statement are UNKNOWN, and abort the moment the head reads one.
            This is what tells us the rule does not secretly read past `l3`
            or past the right end.

    python3 tools/counters/drz6lem.py
"""
import argparse
from collections import defaultdict
from drz6cc import TAB, LAB, cstep, csim, chd, ctl

UNK = 9  # a cell whose value the lemma does not fix


def rep(s, n):
    return (s,) * n


def branch(l):
    """The claimed successor left word and step count, or None."""
    z = 0
    while z < len(l) and l[z] == 0:
        z += 1
    if z >= len(l):
        return None                      # no S1: B sweeps off the end
    l2 = l[z + 1:]
    if chd(l2) == 1:
        return rep(1, z) + (0, 0) + tuple(ctl(l2)), 2 * z + 4
    if z >= 1:
        return rep(1, z - 1) + (0, 0, 1) + tuple(ctl(l2)), 2 * z + 4
    return (0, 0, 1, 1) + tuple(ctl(l2)), 10


def check_orbit(T):
    ev = list(csim(T))
    hits = [(n, c) for n, c in ev if c[0] == 3 and c[1][1] == 0]
    bad = 0
    counts = defaultdict(int)
    for (n0, c0), (n1, c1) in zip(hits, hits[1:]):
        l = c0[1][0]
        b = branch(l)
        if b is None:
            print("  NO BRANCH at n=%d l=%s" % (n0, l))
            bad += 1
            continue
        lp, cost = b
        z = 0
        while z < len(l) and l[z] == 0:
            z += 1
        kind = ('i' if chd(l[z + 1:]) == 1 else ('ii' if z >= 1 else 'iii'))
        counts[kind] += 1
        if c1 != (3, (lp, 0, ())) or n1 - n0 != cost:
            bad += 1
            if bad < 6:
                print("  MISMATCH n=%d branch %s\n    l =%s\n    got %s @+%d"
                      "\n    want %s @+%d"
                      % (n0, kind, l, c1, n1 - n0, (3, (lp, 0, ())), cost))
    print("  orbit: %d landmark transitions, %d mismatches; branches %s"
          % (len(hits) - 1, bad, dict(counts)))
    return hits


def run_unknown(c, limit):
    """Step until the head would READ an UNK cell.  Returns (config, steps) or
    ('READ-UNKNOWN', steps)."""
    for n in range(limit):
        q, (l, h, r) = c
        if h == UNK:
            return 'READ-UNKNOWN', n
        c = cstep(c)
    return c, limit


def check_ctx():
    """Every rule, over ALL instantiations of the unknown context: l3 is a
    single UNK cell standing for an arbitrary tail, and the right half-tape
    beyond what the rule names is UNK too."""
    print("  unknown-context check (l3 = one UNK cell, right tail UNK):")
    ok = True
    for z in range(0, 7):
        cases = [
            ('i',   rep(0, z) + (1, 1, UNK)),
            ('ii',  rep(0, z) + (1, 0, UNK)) if z >= 1 else None,
            ('iii', (1, 0, UNK)) if z == 0 else None,
            # l2 = [] : the chd/ctl-of-nil cases the lemma must also cover
            ('ii0', rep(0, z) + (1,)) if z >= 1 else None,
            ('iii0', (1,)) if z == 0 else None,
        ]
        for case in cases:
            if case is None:
                continue
            kind, l = case
            b = branch(tuple(x if x != UNK else 0 for x in l))
            # recompute the claimed successor keeping UNK symbolic
            zz = 0
            while zz < len(l) and l[zz] == 0:
                zz += 1
            l2 = l[zz + 1:]
            if chd(l2) == 1:
                lp, cost = rep(1, zz) + (0, 0) + tuple(ctl(l2)), 2 * zz + 4
            elif zz >= 1:
                lp, cost = (rep(1, zz - 1) + (0, 0, 1) + tuple(ctl(l2)),
                            2 * zz + 4)
            else:
                lp, cost = (0, 0, 1, 1) + tuple(ctl(l2)), 10
            # right half-tape: the rule says nothing about it, so make the
            # very first cell past the head UNK.
            c = (3, (l, 0, (UNK,)))
            got, n = run_unknown(c, cost)
            want = (3, (lp, 0, ()))
            # with an UNK right tail the reached right list is (UNK,) too
            wantU = (3, (lp, 0, (UNK,)))
            mark = "OK " if (got in (want, wantU) and n == cost) else "BAD"
            if mark == "BAD":
                ok = False
            print("    z=%d %-5s l=%-22s -> %-30s +%-3d %s"
                  % (z, kind, ''.join(str(x) for x in l),
                     ('READ-UNKNOWN' if got == 'READ-UNKNOWN'
                      else ''.join(str(x) for x in got[1][0])), n, mark))
    # and the same with a LITERAL blank right tail
    print("  same rules with an explicit-blank right tail ([] and [S0]):")
    for z in (0, 1, 3):
        for kind, l in (('i', rep(0, z) + (1, 1, UNK)),
                        ('ii/iii', rep(0, z) + (1, 0, UNK))):
            zz = 0
            while zz < len(l) and l[zz] == 0:
                zz += 1
            l2 = l[zz + 1:]
            if chd(l2) == 1:
                lp, cost = rep(1, zz) + (0, 0) + tuple(ctl(l2)), 2 * zz + 4
            elif zz >= 1:
                lp, cost = (rep(1, zz - 1) + (0, 0, 1) + tuple(ctl(l2)),
                            2 * zz + 4)
            else:
                lp, cost = (0, 0, 1, 1) + tuple(ctl(l2)), 10
            for tail in ((), (0,), (0, 0)):
                got, n = run_unknown((3, (l, 0, tail)), cost)
                good = (got != 'READ-UNKNOWN' and got[0] == 3
                        and got[1][0] == lp and got[1][1] == 0
                        and all(x == 0 for x in got[1][2]) and n == cost)
                if not good:
                    ok = False
                    print("    BAD z=%d %s tail=%s -> %s +%d"
                          % (z, kind, tail, got, n))
    print("    all unknown-context / blank-tail checks pass: %s" % ok)
    return ok


def check_invariant(hits):
    """What predicate on l is closed under the three branches?"""
    Ws = [tuple(reversed(c[1][0])) for _, c in hits]
    Ws = [w[next((k for k, x in enumerate(w) if x == 1), 0):] for w in Ws]
    print("  landmark words W (leading blanks stripped):")
    print("    distinct 2-prefixes: %s" % sorted({w[:2] for w in Ws}))
    print("    distinct 3-prefixes: %s" % sorted({w[:3] for w in Ws}))
    print("    distinct 4-prefixes: %s" % sorted({w[:4] for w in Ws}))
    print("    any W of the form 1 0^z ?  %s"
          % sorted({len(w) for w in Ws if all(x == 0 for x in w[1:])}))
    print("    any W of the form 101 0^z ? %s"
          % sorted({len(w) for w in Ws
                    if len(w) >= 3 and w[:3] == (1, 0, 1)
                    and all(x == 0 for x in w[3:])}))
    # the two dangerous shapes for l
    danger1 = [c[1][0] for _, c in hits
               if len(c[1][0]) >= 2 and c[1][0][0] == 1 and c[1][0][1] == 1
               and all(x == 0 for x in c[1][0][2:])]
    print("    l = S1::S1::(all zeros)  (branch (i) kills the last S1): %d"
          % len(danger1))
    print("    every l contains an S1: %s"
          % all(1 in c[1][0] for _, c in hits))
    print("    every l ends (head-outward) in S1: %s"
          % all(c[1][0] and c[1][0][-1] == 1 for _, c in hits))
    print("    every l ends (head-outward) in S0,S1: %s"
          % all(len(c[1][0]) >= 2 and c[1][0][-2:] == (0, 1) for _, c in hits))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=300000)
    a = ap.parse_args()
    print("=" * 72)
    print("Drozd's sixth  1RB0RD_1LB1LC_1RC0RA_0LB1RD   D0-landmark rules")
    hits = check_orbit(a.steps)
    check_ctx()
    check_invariant(hits)


if __name__ == '__main__':
    main()
