#!/usr/bin/env python3
"""Mirror of the COQ-SIDE composition lemmas for wave4 #15, checked against
tools/counters/lap15.py's venc and against probe15's raw simulator.

Everything here mirrors exactly what the Coq will state:
  wblocks, owtape, owcost, owdeb, lay, bta, back, bcost, btail, Scan
and the two decomposition equations plus the venc arithmetic.
UNTRUSTED (tools/), like the rest -- the kernel re-checks all of it.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe15 import cstep, chd, ctl, A, B, C, D, S0, S1
from lap15 import venc

# ---- the Coq definitions, transcribed -------------------------------------

def wblocks(v):
    out = []
    for x in v:
        out += [S1] * x + [S0]
    return out

def owtape(l, R):
    out = []
    for a in l:
        out += [S1] * (2 * a + 2) + [S0]
    return out + R

def owcost(l):
    return sum(6 * a + 5 for a in l)

def lay(k, L):
    return [S1, S1] * k + L

def owdeb(l, M):
    for a in l:
        M = [S0, S1, S1] + lay(a, M)
    return M

def bta(l, R):
    out = []
    for a in l:
        out += [S1] * (2 * a) + [S0, S1, S1]
    return out + R

def back(Dd, R):
    while True:
        if Dd[:3] == [S0, S1, S1]:
            R = [S0, S1, S1] + R
            Dd = Dd[3:]
        elif Dd[:1] == [S1]:
            R = [S1] + R
            Dd = Dd[1:]
        else:
            return [S1] + R

def bcost(Dd):
    n = 0
    while True:
        if Dd[:3] == [S0, S1, S1]:
            n += 7
            Dd = Dd[3:]
        elif Dd[:1] == [S1]:
            n += 1
            Dd = Dd[1:]
        else:
            return n + 1

def pod(p):
    return p % 2

def btail(a, rest):
    if not rest:
        return [2 * a + 2, 2]
    return [2 * a + 3, rest[0] + 1] + rest[1:]

def scan(bl):
    """Scan bl l a rest bl' -- walk the even blocks, stop at the first odd."""
    l = []
    i = 0
    while i < len(bl) and bl[i] % 2 == 0:
        l.append((bl[i] - 2) // 2)
        i += 1
    if i == len(bl):
        return None
    a = (bl[i] - 1) // 2
    rest = bl[i + 1:]
    return l, a, rest, [2 * b + 2 for b in l] + btail(a, rest)

def Cf15(p):
    return (C, [], S0, [S1] * (1 + pod(p)) + [S0] + wblocks(venc(p)))

# ---- the checks -----------------------------------------------------------

MM = [S0, S1, S1]          # M, the left context entry5 leaves behind

def check(p):
    bad = []
    bl = venc(p)
    if p % 2 == 0:
        # rule A: venc (xO r) = c :: t, venc (xI r) = S c :: t, c >= 1
        w = venc(p + 1)
        if not (bl and w and w[0] == bl[0] + 1 and w[1:] == bl[1:] and bl[0] >= 1):
            bad.append('p=%d venc_xO_xI: %s -> %s' % (p, bl, w))
        return bad
    # odd: the Scan decomposition
    sc = scan(bl)
    if sc is None:
        return ['p=%d: no odd block in %s' % (p, bl)]
    l, a, rest, blp = sc
    if blp != venc(p + 1):
        bad.append('p=%d Scan_venc: got %s want %s' % (p, blp, venc(p + 1)))
    if rest and rest[0] < 1:
        bad.append('p=%d hdok: %s' % (p, rest))
    # Lemma Scan_in
    if wblocks(bl) != owtape(l, [S1] * (2 * a + 1) + [S0] + wblocks(rest)):
        bad.append('p=%d Scan_in' % p)
    # Lemma Scan_out
    if wblocks(blp) != owtape(l, wblocks(btail(a, rest))):
        bad.append('p=%d Scan_out' % p)
    # Lemma owtape_bta
    if [S1, S1] + bta(l, [S0]) != owtape(l, [S1, S1, S0]):
        bad.append('p=%d owtape_bta' % p)

    # the assembled lap, as the Coq will chain it
    n1 = 5 + owcost(l) + 6 * a
    if rest:
        n2 = 8
        R2 = [S1] * (rest[0] - 1) + [S0] + wblocks(rest[1:])
        Dd = [S1] + lay(a, owdeb(l, MM))
        tail = [S0, S1, S1] + R2
    else:
        n2 = 6
        Dd = [S0, S1, S1] + lay(a, owdeb(l, MM))
        tail = [S0]
    n = n1 + n2 + bcost(Dd)
    got = (C, [], S0, back(Dd, tail))
    if got != Cf15(p + 1):
        bad.append('p=%d lap config\n  got  %s\n  want %s' % (p, got, Cf15(p + 1)))
    # against the raw simulator
    c = (C, ([], S0, Cf15(p)[3]))
    for _ in range(n):
        c = cstep(c)
        if c is None:
            bad.append('p=%d: machine died' % p)
            return bad
    q, (L, h, R) = c
    if (q, L, h, R) != got:
        bad.append('p=%d steps=%d: sim says %s' % (p, n, (q, L, h, R)))
    # ...and that n is exactly the lap (n-1 is not an anchor)
    c = (C, ([], S0, Cf15(p)[3]))
    for t in range(1, n):
        c = cstep(c)
        q, (L, h, R) = c
        if q == C and L == [] and h == S0 and R and R[0] == S1:
            bad.append('p=%d: earlier anchor at t=%d' % (p, t))
            break
    return bad


def main():
    maxp = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    bad = []
    for p in range(2, maxp):
        bad += check(p)
        if len(bad) > 6:
            break
    print('#15 composition layer, p = 2 .. %d' % (maxp - 1))
    for b in bad[:6]:
        print('  FAIL %s' % b)
    print('  %s' % ('OK -- Scan/btail/venc arithmetic and the assembled lap agree'
                    if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
