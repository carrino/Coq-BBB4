#!/usr/bin/env python3
"""Tower #20's INVARIANT, found: the descent-tower descriptor.

`inv20.py` established that the system is SELF-SIMILAR -- four laps at one
level are one lap one level down -- and that this rules out every regular or
bounded-depth invariant.  What it did not notice is that the descent CLOSES:
the level boots CYCLE.  Concretely, with X(t) = [2;1] if t = [] else
(t0+3) :: t[1:], the four phase identities

    nv0 ([1;1] ++ U) = [4] ++ U
    nv0 ([4]   ++ U) = [1;2] ++ nv0 U
    nv0 ([1;2] ++ S) = [5] ++ S
    nv0 ([5]   ++ S) = [1;1] ++ X S

are UNCONDITIONAL identities of nv0, the four-lap block maps U to
X (nv0 U), and when U = 4 :: x that is 4 :: nv x -- the level below is an
nv-orbit.  The level-0 boot [1;4] reaches, after two boot laps and two
pre-descent blocks (U = [1;2;1], then [8;1]), the descended U = 4::[1;2;2;1];
and the boot [1;2;2;1] reaches, after two boot laps and one pre-descent
block (U = [5;1]), the descended U = 4::[1;4] -- the level-0 boot again.

So every word the orbit ever visits is the decode of a FINITE nested
descriptor (the mutual inductive Vd/Ud in Tower_20.v), nv acts on
descriptors as a structural map, and "is a decode" is the invariant: it
holds at the boot, is preserved by nv, and every decode has an odd entry
and no zero entry.  This file checks, in the EXACT form stated in Coq:

  1. dec/step mirror: the descriptor orbit from (0, VA0) reproduces the raw
     nv orbit word-for-word (default 4000 laps), and hasodd/nonzero hold;
  2. the step identity nv0 (decV v) = decV (stepV v) and
     X (nv0 (decU u)) = decU (stepU u) on randomly generated descriptors;
  3. the word-successor lemmas behind the lap glue, exhaustively over
     K-prefixes and turn tails:
       enc (Dmid K k)  (wruns ((n2+1+3) :: t2)) = wruns (nv0 (wev K ((2k+1) :: n2+1 :: t2)))
       enc (Dmidz K k) [1] ++ [0]               = wruns (nv0 (wev K [2k+1]))

UNTRUSTED, like everything under tools/.  Usage: `python3 desc20.py`.
"""
import itertools
import random
import sys

# ---------------------------------------------------------------- the model
def nv0(w):
    out = []
    while True:
        if not w:
            return out
        n, t = w[0], w[1:]
        if n % 2 == 0:
            out += [1] * (n // 2 - 1) + [2]
            w = t
            continue
        if not t:
            return out + [1] * (n // 2) + [2, 1]
        return out + [1] * (n // 2) + [t[0] + 3] + t[1:]


def nv(w):
    return [2] + nv0(w)


def X(t):
    return [2, 1] if not t else [t[0] + 3] + t[1:]


def hasodd(w):
    return any(x % 2 for x in w)


# ------------------------------------------------- the descriptor (Vd / Ud)
# Vd: ('A0',) ('A1',) ('D0', m) ('D1', m) ('P', p, u)   p in 0..3
# Ud: ('UA2',) ('UA3',) ('UC0', n) ('UC1', n) ('UD0', m) ('UD1', m)
#     ('UD', a, v)
def rep2(n, t):
    return [2] * n + t


def decV(v):
    tag = v[0]
    if tag == 'A0':
        return [1, 4]
    if tag == 'A1':
        return [7]
    if tag == 'D0':
        return [1, 5] + rep2(v[1], [1])
    if tag == 'D1':
        return [8] + rep2(v[1], [1])
    _, p, u = v
    U = decU(u)
    return [[1, 1] + U, [4] + U, [1, 2] + nv0(U), [5] + nv0(U)][p]


def decU(u):
    tag = u[0]
    if tag == 'UA2':
        return [1, 2, 1]
    if tag == 'UA3':
        return [8, 1]
    if tag == 'UC0':
        return rep2(u[1], [1])
    if tag == 'UC1':
        return [5] + rep2(u[1], [1])
    if tag == 'UD0':
        return [1] + rep2(u[1] + 2, [1])
    if tag == 'UD1':
        return [8] + rep2(u[1] + 1, [1])
    _, a, v = u
    return [4] + rep2(a, decV(v))


def stepV(v):
    tag = v[0]
    if tag == 'A0':
        return ('A1',)
    if tag == 'A1':
        return ('P', 0, ('UA2',))
    if tag == 'D0':
        return ('D1', v[1])
    if tag == 'D1':
        return ('P', 0, ('UD0', v[1]))
    _, p, u = v
    return ('P', p + 1, u) if p < 3 else ('P', 0, stepU(u))


def stepU(u):
    tag = u[0]
    if tag == 'UA2':
        return ('UA3',)
    if tag == 'UA3':
        return ('UD', 0, ('P', 0, ('UC0', 2)))
    if tag == 'UC0':
        return ('UC1', u[1])
    if tag == 'UC1':
        return ('UD', 0, ('A0',)) if u[1] == 0 else ('UD', 0, ('D0', u[1] - 1))
    if tag == 'UD0':
        return ('UD1', u[1])
    if tag == 'UD1':
        return ('UD', 0, ('P', 0, ('UC0', u[1] + 3)))
    _, a, v = u
    return ('UD', a + 1, stepV(v))


def rand_desc(rng, depth):
    """A random Vd of nesting depth <= depth."""
    if depth == 0 or rng.random() < 0.3:
        c = rng.choice(['A0', 'A1', 'D0', 'D1'])
        return (c,) if c in ('A0', 'A1') else (c, rng.randint(0, 6))
    r = rng.random()
    if r < 0.4:
        c = rng.choice(['UA2', 'UA3', 'UC0', 'UC1', 'UD0', 'UD1'])
        u = (c,) if c in ('UA2', 'UA3') else (c, rng.randint(0, 6))
    else:
        u = ('UD', rng.randint(0, 5), rand_desc(rng, depth - 1))
    return ('P', rng.randint(0, 3), u)


def subs_of(v):
    yield ('V', v)
    if v[0] == 'P':
        u = v[2]
        yield ('U', u)
        if u[0] == 'UD':
            yield from subs_of(u[2])


# ---------------------------------------------------------------- 1. mirror
def check_mirror(laps=4000):
    a, v = 0, ('A0',)
    w = [2] * a + decV(v)
    bad = []
    for n in range(laps):
        if not hasodd(w):
            bad.append('lap %d: no odd' % n)
            break
        if any(x == 0 for x in w):
            bad.append('lap %d: zero entry' % n)
            break
        wn = nv(w)
        a, v = a + 1, stepV(v)
        w2 = [2] * a + decV(v)
        if wn != w2:
            bad.append('lap %d: nv %s... != decode %s...' % (n, wn[:8], w2[:8]))
            break
        w = wn
    print('#20 descriptor orbit = nv orbit, hasodd, nonzero, %d laps: %s'
          % (laps, 'OK' if not bad else bad[0]))
    return bad


# ---------------------------------------------- 2. the step identity, random
def check_step(trials=20000, seed=1):
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        for sort, d in subs_of(rand_desc(rng, 6)):
            if sort == 'V':
                if nv0(decV(d)) != decV(stepV(d)):
                    bad.append(('V', d))
            else:
                if X(nv0(decU(d))) != decU(stepU(d)):
                    bad.append(('U', d))
            if bad:
                break
        if bad:
            break
    print('#20 step identity nv0.decV = decV.stepV (and U), %d random'
          ' descriptors: %s' % (trials, 'OK' if not bad else str(bad[0])))
    return bad


# ------------------------------------- 3. the word-successor (enc) mirrors
# CTape-faithful enc over the Sym lists, exactly as in Tower_20.v.
def wruns(w):
    out = []
    for n in w:
        out += [1] * n + [0]
    return out


def dbl(k, L):
    return [1, 0] * k + L


def arep(k, M):
    return [0, 1] * k + M


def rideW(K):
    # rideW (k :: r) = rideW r ++ dbl k [S1], mirrored exactly
    if not K:
        return []
    return rideW(K[1:]) + dbl(K[0], [1])


def Dmid(K, k):
    return arep(k, []) + rideW(K)


def Dmidz(K, k):
    return dbl(k + 1, [1]) + rideW(K)


def enc(D, R):
    while True:
        if len(D) >= 3 and D[0] == 1 and D[1] == 0 and D[2] == 1:
            D, R = D[3:], [1, 1, 0] + R
            continue
        if len(D) >= 2 and D[0] == 0 and D[1] == 1:
            D, R = D[2:], [1, 0] + R
            continue
        return R


def wev(K, t):
    return [2 * k for k in K] + t


def check_enc(maxk=4, seed=2):
    bad = []
    Ks = [list(p) for L in range(0, 4) for p in itertools.product([1, 2, 3, 4], repeat=L)]
    tails = [list(p) for L in range(0, 3) for p in itertools.product([1, 2, 5, 8], repeat=L)]
    cnt = 0
    for K in Ks:
        for k in range(maxk + 1):
            # end branch
            lhs = enc(Dmidz(K, k), [1]) + [0]
            rhs = wruns(nv0(wev(K, [2 * k + 1])))
            if lhs != rhs:
                bad.append(('end', K, k))
                break
            # ne branch
            for n2 in range(4):
                for t2 in tails:
                    cnt += 1
                    lhs = enc(Dmid(K, k), wruns([n2 + 1 + 3] + t2))
                    rhs = wruns(nv0(wev(K, [2 * k + 1, n2 + 1] + t2)))
                    if lhs != rhs:
                        bad.append(('ne', K, k, n2, t2))
                        break
                if bad:
                    break
            if bad:
                break
        if bad:
            break
    print('#20 word-successor: enc(Dmid/Dmidz) = wruns(nv0 . wev), %d'
          ' contexts: %s' % (cnt, 'OK' if not bad else str(bad[0])))
    return bad


def main():
    bad = []
    bad += check_mirror()
    bad += check_step()
    bad += check_enc()
    print('#20 desc: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
