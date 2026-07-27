#!/usr/bin/env python3
"""The sweep inductions, the three rules and the composed lap of
1RB1LD_1RC0RB_1LA0RC_0LD0LA (double #32), each checked against the
CTape-faithful mirror in probe32b.py.

`gadgets32.py` is the differential check for the nine step gadgets; this is
the same check one level up -- every remaining Coq statement in
theories/Machines/Counters/Double_32.v, in the exact form it is stated
there, before any of it was written.  Two of the nine gadgets were wrong on
first reading of the traces and the gadget checker caught both; this file is
what keeps the assemblies honest in the same way.

The Coq names are in the labels, so a failure here points at one lemma:

  rcs/retsw/b1s/d0s  the four sweep inductions
  R1/R2/R3           the three rule lemmas
  lap                Cf32 a --lapn a--> Cf32 (next32 a)

See docs/HOLDOUTS_MXDYS_SN.md section 5b.  UNTRUSTED, like everything
under tools/.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe32b import cstep, chd, ctl, A, B, C, D, S0, S1, c0

NAMES = 'ABCD'


def T(n, c):
    for _ in range(n):
        c = cstep(c)
        if c is None:
            return None
    return c


def show(c):
    if c is None:
        return 'None'
    q, (L, h, R) = c
    return '%s %s[%s]%s' % (NAMES[q], ''.join(map(str, reversed(L))), h,
                            ''.join(map(str, R)))


# -- the Coq definitions, mirrored ------------------------------------------

def comb(j, X):
    return [S0, S0, S1] * j + X


def outp(k, X):
    return [S0, S1, S0] * k + X


def inp(k, X):
    return [S1, S0, S1] * k + X


def rp(x, k):
    return [x] * k


def wden(L):
    out = []
    for (a, b) in L:
        out += rp(S0, a) + rp(S1, b)
    return out


def nrm(L):
    if len(L) >= 2 and L[1][0] == 0:
        return [(L[0][0], L[0][1] + L[1][1])] + L[2:]
    return L


def dec2(L):
    return [(L[0][0] - 2, L[0][1])] + L[1:] if L else []


def nextL(L):
    m = L[0][1]
    return nrm([(1, 4)] + nrm([(m - 4, 2)] + dec2(L[1:])))


def Cf32(j, L):
    W = comb(j, wden(L))
    return (A, ([], chd(W), ctl(W)))


def lapn(j, L):
    return 24 * j + 2 * L[0][1] + 29


# -- the harness ------------------------------------------------------------

BAD = []


def chk(nm, n, start, want, ctx=''):
    got = T(n, start)
    if got != want:
        BAD.append(nm)
        if len(BAD) <= 6:
            print('  FAIL %-6s %s  (%d steps)\n    from %s\n    got  %s\n'
                  '    want %s' % (nm, ctx, n, show(start), show(got),
                                   show(want)))


Ls = [[], [S1], [S0, S1], [S1, S0, S1, S1], [S0, S1, S1, S0, S1, S1, S1]]
Zs = [[], [S1], [S0, S0, S1], [S1, S1], [S0, S1, S0, S0, S1, S1]]


def sweeps():
    """rcs, retsw, b1s, d0s -- the four inductions, tails universal."""
    for k in range(0, 7):
        for L in Ls:
            for Z in Zs:
                chk('rcs', 5 * k, (A, (L, S0, [S1] + outp(k, Z))),
                    (A, (inp(k, L), S0, [S1] + Z)), 'k=%d' % k)
                M = inp(k, [S1, S1])
                chk('retsw', 3 * k + 2, (A, (ctl(M), chd(M), Z)),
                    (A, ([], S0, [S0, S1] + comb(k, Z))), 'k=%d' % k)
                chk('retsw1', 3 * (k + 1) + 2,
                    (A, ([S0, S1] + inp(k, [S1, S1]), S1, Z)),
                    (A, ([], S0, [S0, S1] + comb(k + 1, Z))), 'k=%d' % k)
                chk('b1s', k, (B, (L, S1, rp(S1, k) + Z)),
                    (B, (rp(S0, k) + L, S1, Z)), 'k=%d' % k)
                chk('d0s', k, (D, (rp(S0, k) + L, S0, Z)),
                    (D, (L, S0, rp(S0, k) + Z)), 'k=%d' % k)
                chk('out32', 4 + 5 * k, (A, (L, S0, [S0, S1, S0] + outp(k, Z))),
                    (A, (inp(k, [S1, S1] + L), S0, [S1] + Z)), 'k=%d' % k)


# R1's tail is arbitrary given chd Y = chd (ctl Y) = S0 -- which is exactly
# "the next block starts with two blanks, or there is no next block".
Ys = [[], [S0], [S0, S0], [S0, S0, S1, S1], [S0, S0, S1, S1, S0, S0, S1, S1],
      [S0, S0, S0, S0, S1, S1, S0, S0, S1, S1]]
Ts = [[], [S1], [S1, S1], [S0, S0, S1, S1], [S1, S1, S0, S0, S1, S1], [S0, S1, S1]]


def rules():
    """R1, R2, R3 exactly as stated in Double_32.v."""
    for i in range(0, 6):
        for m in range(0, 11):
            for Y in Ys:
                if chd(Y) != S0 or chd(ctl(Y)) != S0:
                    continue
                chk('R1', 8 * (i + 1) + 2 * m + 5,
                    (A, ([], S0, [S0, S1] + comb(i, [S0] + rp(S1, m) + Y))),
                    (A, ([], S0, [S0, S1] + comb(i, rp(S0, m + 2) + [S1, S1]
                                                 + ctl(ctl(Y))))),
                    'i=%d m=%d' % (i, m))
        for Tl in Ts:
            chk('R2', 8 * (i + 1) + 5,
                (A, ([], S0, [S0, S1] + comb(i, [S0, S0, S0] + Tl))),
                (A, ([], S0, [S0, S1] + comb(i + 1, [S1] + Tl))), 'i=%d' % i)
            chk('R3', 8 * (i + 2) + 11,
                (A, ([], S0, [S0, S1] + comb(i + 1, [S1, S0, S0, S0] + Tl))),
                (A, ([], S0, [S0, S1] + comb(i + 1,
                                             [S0, S1, S1, S1, S1] + Tl))),
                'i=%d' % i)


def inv_words():
    """Every block word the invariant admits, up to the sizes below."""
    tails = [[], [(2, 2)], [(4, 2)], [(2, 4)], [(2, 2), (2, 2)],
             [(4, 4), (2, 2)], [(6, 2), (2, 4)]]
    return [[(1, m)] + t for m in (4, 6, 8, 10, 12) for t in tails]


def lap():
    """Cf32 a --lapn a--> Cf32 (next32 a), and the invariant survives it."""
    def ok(L):
        (a, m) = L[0]
        if a != 1 or m < 4 or m % 2:
            return False
        return all(p >= 2 and q >= 2 and p % 2 == 0 and q % 2 == 0
                   for (p, q) in L[1:])
    for j in range(1, 8):
        for L in inv_words():
            assert ok(L), L
            chk('lap', lapn(j, L), Cf32(j, L), Cf32(j + 1, nextL(L)),
                'j=%d L=%s' % (j, L))
            if not ok(nextL(L)):
                BAD.append('Inv32_next')
                print('  FAIL Inv32_next  %s -> %s' % (L, nextL(L)))
    # ...and iterated, so the whole orbit is covered, not just one step
    j, L = 1, [(1, 4)]
    c = Cf32(j, L)
    for _ in range(40):
        c = T(lapn(j, L), c)
        j, L = j + 1, nextL(L)
        if c != Cf32(j, L):
            BAD.append('lap-orbit')
            print('  FAIL lap-orbit at j=%d L=%s\n    got  %s\n    want %s'
                  % (j, L, show(c), show(Cf32(j, L))))
            break


def boot():
    """The boot constant is exact: 24 steps, and no neighbour works."""
    a0 = Cf32(1, [(1, 4)])
    if T(24, c0) != a0:
        BAD.append('boot32')
        print('  FAIL boot32  step 24 is not the first anchor')
    for t in (23, 25):
        if T(t, c0) == a0:
            BAD.append('boot32-exact')
            print('  FAIL boot32  step %d also matches' % t)


def main():
    for f in (sweeps, rules, lap, boot):
        n = len(BAD)
        f()
        print('  %-8s %s' % (f.__name__ + ':',
                             'OK' if len(BAD) == n else 'FAILED'))
    print('#32 rules/sweeps/lap: %s'
          % ('OK' if not BAD else '%d FAILURES (%s)'
             % (len(BAD), ', '.join(sorted(set(BAD))))))
    return 1 if BAD else 0


if __name__ == '__main__':
    sys.exit(main())
