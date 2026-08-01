#!/usr/bin/env python3
"""UNTRUSTED (tools/): check, against the REAL machine, the whole proof chain
that is about to be written in Coq for Drozd's sixth row.

Anchor family     Cf t = G(4t+1),   G z = E (rep S0 z ++ [S1]),
                  E l  = (StD, (l, S0, [])).

Claimed chain (each arrow a lemma):

  Godd    G(2b+1)            -> G(2b+2)                 R_ii ; Zdown b
  Peven   G(4t+2)            -> Q(2t,0)                 R_ii ; Zdown 2t
          Q(m+1,j)           -> Q(m,j+1)                R_ii ; Zdown m
          Q(0,j)             -> K(0,j)                  R_iii ; R_i ; Zdown 1
          K(s,i+2)           -> K(s+1,i)                R_ii ; Zdown ; R_i ; Zdown
          K(s,0)             =  G(4s+5)

  Q m j = E (rep S0 (2m) ++ [S1;S0;S0;S1] ++ rep01 j)
  K s i = E (rep S0 (4s+5) ++ [S1] ++ rep01 i)
  rep01 j = j copies of [S0;S1]

Every arrow is run on the faithful `cstep` simulator and its END CONFIGURATION
compared cell for cell.

    python3 tools/counters/drz6chain.py
"""
import argparse
from drz6cc import cstep, csim, LAB


def E(l):
    return (3, (tuple(l), 0, ()))


def rep(s, n):
    return (s,) * n


def rep01(j):
    return (0, 1) * j


def G(z):
    return E(rep(0, z) + (1,))


def Q(m, j):
    return E(rep(0, 2 * m) + (1, 0, 0, 1) + rep01(j))


def K(s, i):
    return E(rep(0, 4 * s + 5) + (1,) + rep01(i))


def run(c, limit=4 * 10 ** 7):
    """Run until the next D0 landmark that is NOT the start; return (c', n)."""
    n = 0
    while n < limit:
        c = cstep(c)
        n += 1
        if c[0] == 3 and c[1][1] == 0 and c[1][2] == ():
            return c, n
    return None, n


def reach(c0, c1, limit=4 * 10 ** 7):
    """Run c0 forward looking for c1; return steps or None."""
    c, n = c0, 0
    if c == c1:
        return 0
    while n < limit:
        c = cstep(c)
        n += 1
        if c == c1:
            return n
    return None


# ---- the single-cell rules -------------------------------------------------

def R_i(z, X):
    return E(rep(0, z) + (1, 1) + tuple(X)), E(rep(1, z) + (0, 0) + tuple(X)), \
        2 * z + 4


def R_ii(z, l2):
    """l = rep S0 (S z) ++ S1 :: l2  with  chd l2 = S0."""
    l2 = tuple(l2)
    assert (l2[0] if l2 else 0) == 0
    ctl = l2[1:]
    return (E(rep(0, z + 1) + (1,) + l2),
            E(rep(1, z) + (0, 0, 1) + ctl), 2 * z + 6)


def R_iii(l2):
    l2 = tuple(l2)
    assert (l2[0] if l2 else 0) == 0
    return E((1,) + l2), E((0, 0, 1, 1) + l2[1:]), 10


def Zdown(a, X):
    return E(rep(1, 2 * a) + tuple(X)), E(rep(0, 2 * a) + tuple(X))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tmax', type=int, default=5)
    a = ap.parse_args()
    ok = True

    def arrow(name, c0, c1, cost=None):
        nonlocal ok
        n = reach(c0, c1)
        good = n is not None and n > 0 and (cost is None or n == cost)
        ok = ok and good
        print("    %-26s %-34s -> %-34s %s%s"
              % (name, ''.join(map(str, c0[1][0])) or "(nil)",
                 ''.join(map(str, c1[1][0])) or "(nil)",
                 ("+%d" % n) if n is not None else "UNREACHED",
                 "" if good else "   <== BAD"))
        return n

    print("=" * 78)
    print("single-cell rules (spot instances):")
    for z in range(0, 5):
        for X in ((), (1,), (0, 1), (1, 0, 0, 1)):
            c0, c1, cost = R_i(z, X)
            arrow("R_i z=%d X=%s" % (z, X), c0, c1, cost)
    for z in range(0, 4):
        for l2 in ((), (0,), (0, 1), (0, 0, 1)):
            c0, c1, cost = R_ii(z, l2)
            arrow("R_ii z=%d l2=%s" % (z, l2), c0, c1, cost)
    for l2 in ((), (0,), (0, 1), (0, 0, 1), (0, 1, 0, 1)):
        c0, c1, cost = R_iii(l2)
        arrow("R_iii l2=%s" % (l2,), c0, c1, cost)

    print("Zdown a X (all-ones digit word descends to zero):")
    for aa in range(0, 5):
        for X in ((1,), (0, 0, 1), (1, 0, 0, 1)):
            c0, c1 = Zdown(aa, X)
            arrow("Zdown a=%d X=%s" % (aa, X), c0, c1)

    print("Godd  G(2b+1) -> G(2b+2):")
    for b in range(0, 6):
        arrow("b=%d" % b, G(2 * b + 1), G(2 * b + 2))

    print("Peven pieces:")
    for t in range(0, a.tmax):
        arrow("G(4t+2)->Q(2t,0) t=%d" % t, G(4 * t + 2), Q(2 * t, 0))
    for m in range(1, 6):
        for j in range(0, 3):
            arrow("Q(%d,%d)->Q(%d,%d)" % (m, j, m - 1, j + 1),
                  Q(m, j), Q(m - 1, j + 1))
    for j in range(0, 6):
        arrow("Q(0,%d)->K(0,%d)" % (j, j), Q(0, j), K(0, j))
    for s in range(0, 3):
        for i in range(0, 5):
            arrow("K(%d,%d)->K(%d,%d)" % (s, i + 2, s + 1, i),
                  K(s, i + 2), K(s + 1, i))
    print("K(s,0) = G(4s+5):")
    for s in range(0, 5):
        same = K(s, 0) == G(4 * s + 5)
        ok = ok and same
        print("    s=%d  %s" % (s, "OK" if same else "MISMATCH"))

    print("WHOLE LAP  Cf t = G(4t+1) -> G(4(t+1)+1) = G(4t+5):")
    for t in range(0, a.tmax + 2):
        arrow("t=%d" % t, G(4 * t + 1), G(4 * t + 5))

    print("BOOT: blank tape -> Cf 1 = G(5):")
    ev = list(csim(400))
    hit = [n for n, c in ev if c == G(5)]
    print("    G(5) first reached at step %s" % (hit[:1] or "NEVER"))
    ok = ok and bool(hit)

    print("HVIS: from Cf t, states D/B/C/A at offsets 0/1/4t+3/4t+5:")
    for t in range(0, 5):
        c = G(4 * t + 1)
        seen = {}
        cc = c
        for n in range(0, 4 * t + 8):
            seen.setdefault(cc[0], n)
            cc = cstep(cc)
        good = (seen.get(3) == 0 and seen.get(1) == 1
                and seen.get(2) == 4 * t + 3 and seen.get(0) == 4 * t + 5)
        ok = ok and good
        print("    t=%d  first offsets %s  %s"
              % (t, {LAB[k]: v for k, v in sorted(seen.items())},
                 "OK" if good else "BAD"))

    print("=" * 78)
    print("ALL CHAIN CHECKS PASS: %s" % ok)


if __name__ == '__main__':
    main()
