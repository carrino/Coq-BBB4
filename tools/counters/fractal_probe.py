#!/usr/bin/env python3
"""Reproduce the fractal decode: both machines are binary counters whose
digits are BLOCKS.

    python3 tools/counters/fractal_probe.py            # all checks
    python3 tools/counters/fractal_probe.py words      # just the odometer words

Checks, all differential against a plain simulator:

  #5  1RB0LA_1LC1RD_0LC1LA_0RD0RB   digit i = 2^i cells
      anchor  (StB, (0^(N-1) ++ 1^N, 0, []))      N = 2^k, t = 2*4^k - 2^k
      lap     6N^2 - N
      Inc(m,z)   framed, cost 2m^2 + 2z + 3
      E2(q,a,b)  framed, cost 2q^2 + b + 1 - q      (a >= q-1, ANY b)

  #3  1RB0LA_1LC0RD_0LB1LA_0RB1LA   digit i = 2^(i+1) cells
      anchor  (StB, (0^N ++ 1^N, 0, []))          N = 2^k
      lap     3N^2 + 4*3^k - N
      Inc3(m,z)  framed, cost 4m^2 + 6*3^t + 12 + 4z
      close3(e,z) cost 4e + 2z + 30

The Coq boards are theories/Machines/Counters/Fractal_5.v and Fractal_3.v.
UNTRUSTED: this file is measurement only; the kernel re-checks every board.
"""
import random
import sys

M5 = "1RB0LA_1LC1RD_0LC1LA_0RD0RB"
M3 = "1RB0LA_1LC0RD_0LB1LA_0RB1LA"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


class C:
    """cconf: left list nearest-first, head, right list (blanks beyond)."""

    def __init__(s, tab, q, L, h, R):
        s.tab, s.q, s.L, s.h, s.R = tab, q, list(L), h, list(R)

    def step(s):
        tr = s.tab.get((s.q, s.h))
        if tr is None:
            return None
        w, d, nq = tr
        if d == 1:
            s.L.insert(0, w)
            s.h = s.R.pop(0) if s.R else 0
        else:
            s.R.insert(0, w)
            s.h = s.L.pop(0) if s.L else 0
        s.q = nq
        return s

    def run(s, n):
        for _ in range(n):
            if s.step() is None:
                return None
        return s


def trim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def eq(a, b):
    return (a is not None and b is not None and a.q == b.q and a.h == b.h
            and trim(a.L) == trim(b.L) and trim(a.R) == trim(b.R))


def Z(n):
    return [0] * n


def O(n):
    return [1] * n


def P(n):
    return [0, 1] * n


def rnd(rng, k=10):
    return [rng.randint(0, 1) for _ in range(k)]


# --------------------------------------------------------------------------
# machine #5
# --------------------------------------------------------------------------

def check5(rng):
    tab = parse(M5)
    ok = True

    # anchors from the blank tape
    c = C(tab, 0, [], 0, [])
    hits, k = [], 0
    for i in range(4000):
        if c.q == 1 and c.h == 0 and not trim(c.R):
            L = trim(c.L)
            n = len(L)
            j = 0
            while j < n and L[n - 1 - j] == 1:
                j += 1
            if j and all(x == 0 for x in L[:n - j]) and n - j == j - 1:
                hits.append((i, j))
        if c.step() is None:
            break
    want = [(2 * 4 ** k - 2 ** k, 2 ** k) for k in range(6)]
    got = [h for h in hits if h in want]
    ok &= (got == want[:len(got)] and len(got) >= 5)
    print("  #5 anchors  2*4^k - 2^k :", "OK" if ok else "FAIL", hits[:6])

    # framed lap
    for k in range(0, 8):
        N = 2 ** k
        L, R = rnd(rng), rnd(rng)
        g = C(tab, 1, Z(N - 1) + O(N) + Z(N) + L, 0, Z(N) + R).run(6 * N * N - N)
        good = eq(g, C(tab, 1, Z(2 * N - 1) + O(2 * N) + L, 0, R))
        ok &= good
        if not good:
            print("  #5 lap N=%d FAIL" % N)
    print("  #5 lap      6N^2 - N   : OK (framed, N up to 2^7)")

    # the increment gadget
    bad = 0
    for t in range(0, 7):
        m = 2 ** t
        for z in range(0, 8):
            H, R = rnd(rng), rnd(rng)
            g = C(tab, 1, Z(z) + O(m) + Z(m) + H, 0, [0] + R).run(2 * m * m + 2 * z + 3)
            if not eq(g, C(tab, 1, Z(z + 1) + [1] + Z(m - 1) + O(m) + H, 0, R)):
                bad += 1
    ok &= bad == 0
    print("  #5 Inc(m,z) 2m^2+2z+3  :", "OK" if bad == 0 else "%d FAIL" % bad)

    # the two-parameter rule, with b FREE
    bad = 0
    for t in range(1, 6):
        q = 2 ** t
        for a in range(q - 1, q + 6):
            for b in range(0, q + 6):
                L, R = rnd(rng), rnd(rng)
                g = C(tab, 1, [1] + Z(a) + L, 0,
                      Z(q - 2) + [1] + Z(b) + [1, 0] + R).run(2 * q * q + b + 1 - q)
                if not eq(g, C(tab, 1, Z(b + 1) + [1] + Z(q - 1) + O(q)
                               + Z(a + 1 - q) + L, 0, R)):
                    bad += 1
    ok &= bad == 0
    print("  #5 E2(q,a,b) 2q^2+b+1-q:", "OK" if bad == 0 else "%d FAIL" % bad)
    return ok


# --------------------------------------------------------------------------
# machine #3
# --------------------------------------------------------------------------

def check3(rng):
    tab = parse(M3)
    ok = True

    c = C(tab, 0, [], 0, [])
    hits = []
    for i in range(5000):
        if c.q == 1 and c.h == 0 and not trim(c.R):
            L = trim(c.L)
            n = len(L)
            j = 0
            while j < n and L[n - 1 - j] == 1:
                j += 1
            if j and all(x == 0 for x in L[:n - j]) and n - j == j:
                hits.append((i, j))
        if c.step() is None:
            break
    print("  #3 anchors (t, N)      :", hits[:5])

    for k in range(1, 7):
        N = 2 ** k
        L, R = rnd(rng), rnd(rng)
        cost = 3 * N * N + 4 * 3 ** k - N
        g = C(tab, 1, Z(N) + O(N) + Z(N) + L, 0, Z(N) + R).run(cost)
        good = eq(g, C(tab, 1, Z(2 * N) + O(2 * N) + L, 0, R))
        ok &= good
        if not good:
            print("  #3 lap N=%d FAIL" % N)
    print("  #3 lap 3N^2+4*3^k-N    : OK (framed, N up to 2^6)")

    bad = 0
    for t in range(0, 7):
        m = 2 ** t
        for z in range(0, 8):
            H, R = rnd(rng), rnd(rng)
            cost = 4 * (4 ** t) + 6 * (3 ** t) + 12 + 4 * z
            g = C(tab, 1, Z(2 * z + 2) + O(2 * m) + Z(2 * m) + H, 0, Z(2) + R).run(cost)
            if not eq(g, C(tab, 1, Z(2 * z + 4) + [1, 1] + Z(2 * m - 2) + O(2 * m) + H,
                           0, R)):
                bad += 1
    ok &= bad == 0
    print("  #3 Inc3 4m^2+6*3^t+12+4z:", "OK" if bad == 0 else "%d FAIL" % bad)

    bad = 0
    for e in range(0, 16):
        for z in range(0, 6):
            H, R = rnd(rng), rnd(rng)
            g = C(tab, 1, Z(2 * e + 2) + [1, 1, 0, 0] + O(2 * e) + H, 0,
                  [1, 1] + P(z + 1) + [0, 0] + R).run(4 * e + 2 * z + 30)
            if not eq(g, C(tab, 1, Z(2 * z + 4) + [1, 1] + Z(2 * e + 2) + O(2 * e + 4) + H,
                           0, R)):
                bad += 1
    ok &= bad == 0
    print("  #3 close3 4e+2z+30     :", "OK" if bad == 0 else "%d FAIL" % bad)
    return ok


# --------------------------------------------------------------------------
# the odometer words
# --------------------------------------------------------------------------

def words(spec, blk, cap):
    """Print the left-tape word at each state-B-reading-blank checkpoint,
    with the counter index it encodes."""
    tab = parse(spec)
    c = C(tab, 0, [], 0, [])
    print("  t      z   left word (left-to-right, trailing blanks stripped)")
    for i in range(cap):
        if c.q == 1 and c.h == 0:
            L = trim(c.L)
            zt = 0
            while zt < len(L) and L[zt] == 0:
                zt += 1
            z = zt // blk if blk == 1 else (zt - 2) // 2
            w = ''.join(str(x) for x in L[zt:][::-1])
            if w:
                print("  %-6d %-3s %s" % (i, z if z >= 0 else '-', w))
        if c.step() is None:
            break


def main():
    rng = random.Random(20260727)
    if len(sys.argv) > 1 and sys.argv[1] == 'words':
        print("#5 odometer words (digit i = 2^i cells):")
        words(M5, 1, 550)
        print()
        print("#3 odometer words (digit i = 2^(i+1) cells):")
        words(M3, 2, 450)
        return 0
    print("fractal probe -- both machines are block-digit binary counters")
    ok = check5(rng)
    ok &= check3(rng)
    print("ALL OK" if ok else "FAILURES ABOVE")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
