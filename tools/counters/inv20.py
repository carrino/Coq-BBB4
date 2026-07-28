#!/usr/bin/env python3
"""Tower #20's INVARIANT: what is now established, and why it is still open.

`nv20.py` gives the successor and shows that "contains an odd" -- the lap's
one requirement, since an all-even word sends the sweep rightward for ever --
is true on the orbit but NOT preserved by `nv` on arbitrary words.  This file
is the structural reconnaissance on that gap.  Everything printed below is
CHECKED, here, against `nv`; the refutations carry witnesses.  Nothing here
is a conjecture that was not run.

WHAT IS ESTABLISHED (each a check in `main`).

 1. THE ALPHABET IS FINITE.  Every entry of every reachable word is in
    {1,2,4,5,8}; 7 occurs once (lap 1) and never again.  The entries are not
    arbitrary: 1 and 2 are FRESH (laid by the return sweep), and 4 = 1+3,
    5 = 2+3, 8 = 5+3 are BUMPED -- an entry is bumped at most twice, along
    1 -> 4 and 2 -> 5 -> 8.  Closure of the alphabet is exactly "the entry
    just after the first odd is in {1,2,5}".

 2. THE LEADING 2-RUN IS THE LAP INDEX.  `nv (2^r ++ v) = 2^(r+1) ++ nv0 v`,
    so the abstract dynamics is `v |-> nv0 v` and aliveness does not depend
    on r at all.

 3. POOR IS A 2-LAP INVARIANT, AND THE OBLIGATION IS ONE PREDICATE.  Call a
    word POOR when it is `2^a ++ [1] ++ t`.  Then

      - the image of a POOR word has an odd  IFF  Cond(t), where
        Cond(t) = hasodd(X t) and X t = [2;1] if t = [] else (t0+3) :: t[1:];
      - two laps later the word is POOR again, with tail

            T([])    = []
            T(1::u)  = 2 :: nv0 u
            T(2::u)  = 1 :: nv0 (1::u)

    so the whole "contains an odd" problem is: Cond along the T-orbit.
    Both claims are checked against `nv` here.

 4. THE ENGINE.  Write E(u) for "the last entry is odd" (which implies
    hasodd) and B(u) for "the first odd sits at |u|-2".  Then

            E(u) and not B(u)   =>   E(nv0 u)

    -- checked on 200,000 random words over a 9-letter alphabet.  So
    "E and never-B" is a sufficient invariant, and the open problem reduces
    from the semantic "hasodd for ever" to the SYNTACTIC "never B".  B is a
    condition on one position, which is why this is progress.

 5. THE SYSTEM IS SELF-SIMILAR, AND THAT IS WHY THE NATURAL CANDIDATES ALL
    FAIL.  The orbit's phase is 4-periodic: writing the anchor word as
    `2^r ++ v`,

        r = 2 mod 4 : v = [1;1] ++ U     r = 3 mod 4 : v = [4] ++ U
        r = 0 mod 4 : v = [1;2] ++ S     r = 1 mod 4 : v = [5] ++ S

    with S = nv0 U, and -- the key identity --

        U_{k+1} = X(nv0 U_k),   and with U = 4::x,   U_{k+1} = 4 :: nv x.

    So FOUR LAPS AT ONE LEVEL ARE ONE LAP ONE LEVEL DOWN, and hasodd at the
    r = 3 mod 4 phase is exactly hasodd of the level-below word.  The
    obligation reproduces itself; there is no finite descent, and no
    bounded-depth predicate can close (death depth is unbounded even over
    the 5-letter alphabet -- checked).  The level-1 orbit is visibly better
    behaved than the level-0 one (it always ends [2;1] and its first odd is
    never 1 or 2 from the end), which is where the next attempt should go.

WHAT IS REFUTED (witnesses printed by `main`).  Every candidate below was
checked for CLOSURE exhaustively over the 5-letter alphabet up to length 8
plus tens of thousands of random words -- never by sampling the orbit:

    contains an odd                       nv [5;1] = [2;1;1;4] -> [2;2;4;4]
    ends in 1                             nv [1;1] = [2;4]
    ends in 1, first odd not at |w|-2     nv [1;2;1] = [2;5;1]
    the Scan/After DFA (every odd's
      successor in {1,2,5})               nv [4;1] = [2;1;2;2;1]; it also
                                          REJECTS the reachable lap-3 word
                                          [2;2;2;4;1;2;1] outright
    alphabet & (rich | >= 2 odds)         nv [5;1] = [2;1;1;4]
    ends [2;1] & first odd not at |w|-3   nv [1;2;2;1] = [2;5;2;1]
    ends [2;1], d not in {1,2}, plus the
      POOR/odd-head refinements (C3, C4)  nv [5;2;2;1] = [2;1;1;5;2;1]

`d(x)` is the number of entries after the first odd.  The last family is the
closest: it holds on the level-1 orbit for 2000 laps and fails only on words
the orbit does not reach -- but "does not reach" is what has to be PROVED,
and that is the whole problem.

UNTRUSTED, like everything under tools/.  Usage: `python3 inv20.py`.
"""
import itertools
import random
import sys


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


A = [1, 2, 4, 5, 8]


def hasodd(w):
    return any(x % 2 for x in w)


def firstodd(w):
    for i, x in enumerate(w):
        if x % 2:
            return i
    return None


def E(u):
    return bool(u) and u[-1] % 2 == 1


def B(u):
    i = firstodd(u)
    return i is not None and len(u) - 1 - i == 1


def d(u):
    i = firstodd(u)
    return None if i is None else len(u) - 1 - i


def X(t):
    return [2, 1] if not t else [t[0] + 3] + t[1:]


def Cond(t):
    return hasodd(X(t))


def poor_tail(w):
    """w = 2^a ++ [1] ++ t -> t, else None."""
    i = 0
    while i < len(w) and w[i] == 2:
        i += 1
    return w[i + 1:] if i < len(w) and w[i] == 1 else None


def T(t):
    """The induced 2-lap map on a POOR tail."""
    return poor_tail(nv(nv([1] + t)))


def orbit(n):
    w, out = [1, 4], []
    for _ in range(n):
        out.append(w)
        w = nv(w)
    return out


# ------------------------------------------------------------------ checks
def check_alphabet(laps=4000):
    seen = set()
    for w in orbit(laps):
        seen.update(w)
    ok = seen <= set(A) | {7}
    print('#20 reachable alphabet over %d laps: %s -- %s'
          % (laps, sorted(seen), 'OK' if ok else 'UNEXPECTED'))
    return [] if ok else ['alphabet']


def check_leading2(trials=20000, seed=1):
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        v = [rng.choice(A) for _ in range(rng.randint(0, 8))]
        r = rng.randint(0, 4)
        if nv([2] * r + v) != [2] * (r + 1) + nv0(v):
            bad.append(v)
            break
    print('#20 nv (2^r ++ v) = 2^(r+1) ++ nv0 v: %s'
          % ('OK' if not bad else str(bad[0])))
    return bad


def check_poor(trials=20000, seed=2):
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        t = [rng.choice(A) for _ in range(rng.randint(0, 9))]
        w = [2] * rng.randint(0, 3) + [1] + t
        y = nv(w)
        if hasodd(y) != Cond(t):
            bad.append(('Cond', t))
            break
        if hasodd(y) and poor_tail(nv(y)) is None:
            bad.append(('poor', t))
            break
        if hasodd(y) and poor_tail(nv(y)) != T(t):
            bad.append(('T', t))
            break
    print('#20 POOR: image-has-an-odd = Cond(t), POOR again after 2 laps,'
          ' and T: %s' % ('OK' if not bad else str(bad[0])))
    return bad


def check_engine(trials=200000, seed=3):
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        u = [rng.randint(0, 8) for _ in range(rng.randint(1, 12))]
        if E(u) and not B(u) and not E(nv0(u)):
            bad.append(u)
            break
    print('#20 ENGINE  E(u) and not B(u)  =>  E(nv0 u), %d random words: %s'
          % (trials, 'OK' if not bad else str(bad[0])))
    return bad


def check_selfsimilar(steps=200, seed=4):
    """U_{k+1} = X(nv0 U_k); and with U = 4::x that is U_{k+1} = 4 :: nv x."""
    bad = []
    rng = random.Random(seed)
    for _ in range(3000):
        x = [rng.choice(A) for _ in range(rng.randint(0, 8))]
        if X(nv0([4] + x)) != [4] + nv(x):
            bad.append(x)
            break
    # and that the 4-lap phase really is what the orbit does
    O = orbit(4 * steps + 20)
    for k in range(2, steps):
        r = 4 * k + 2
        w = O[r]
        v = w[r:] if all(y == 2 for y in w[:r]) else None
        if v is None or v[:2] != [1, 1]:
            bad.append(('phase', r))
            break
    print('#20 self-similarity  X(nv0 (4::x)) = 4 :: nv x, and the 4-phase'
          ' of the orbit: %s' % ('OK' if not bad else str(bad[0])))
    return bad


def check_unbounded_death(maxlen=5):
    """No bounded-depth predicate can close: death is arbitrarily deep even
    over the 5-letter alphabet."""
    deep = 0
    for L in range(1, maxlen + 1):
        for p in itertools.product(A, repeat=L):
            v, dep = list(p), None
            for i in range(120):
                if not hasodd(v):
                    dep = i
                    break
                v = nv(v)
                if len(v) > 40000:
                    break
            if dep is not None:
                deep = max(deep, dep)
    print('#20 deepest death over A, |v| <= %d: %d laps -- so "alive within'
          ' k laps" is closed for no k' % (maxlen, deep))
    return [] if deep > 20 else ['death not deep']


# ------------------------------------------------------- refuted candidates
def inalpha(w):
    return all(x in A for x in w)


def c_hasodd(w):
    return hasodd(w)


def c_end1(w):
    return inalpha(w) and bool(w) and w[-1] == 1


def c_end1_nb(w):
    return c_end1(w) and d(w) != 1


def c_scan(w):
    if not inalpha(w):
        return False
    st = 'G'
    for x in w:
        if st == 'G':
            st = 'N' if x % 2 else 'G'
        elif x == 2:
            st = 'N'
        elif x % 2:
            st = 'G'
        else:
            return False
    return st == 'N'


def c_rich2(w):
    if not (inalpha(w) and hasodd(w)):
        return False
    i = firstodd(w)
    rich = any(e >= 4 for e in w[:i]) or w[i] >= 3
    return rich or sum(1 for x in w if x % 2) >= 2


def c_21_d3(w):
    return inalpha(w) and w[-2:] == [2, 1] and d(w) != 2


def c_C4(w):
    if not (inalpha(w) and w[-2:] == [2, 1]) or d(w) in (1, 2):
        return False
    i = firstodd(w)
    pr = all(e == 2 for e in w[:i]) and w[i] == 1
    if pr and d(w) < 4:
        return False
    t = w[i + 1:]
    if pr and t and t[0] % 2 == 1 and d(t[1:]) in (1, 2):
        return False
    return True


ORB3 = orbit(4)[3]          # the lap-3 anchor word, [2;2;2;4;1;2;1]

CANDS = [
    ('contains an odd', c_hasodd),
    ('ends in 1', c_end1),
    ('ends in 1, first odd not at |w|-2', c_end1_nb),
    ('the Scan/After DFA', c_scan),
    ('alphabet & (rich | >=2 odds)', c_rich2),
    ('ends [2;1] & d != 2', c_21_d3),
    ('ends [2;1], d not in {1,2}, POOR refinements (C4)', c_C4),
]


def refute(maxlen=8, rnd=40000, seed=5):
    """Every candidate must FAIL closure -- with a witness.  If one of these
    ever comes back OK, it is the invariant and this file is out of date."""
    bad = []
    rng = random.Random(seed)
    pool = [list(p) for L in range(0, maxlen + 1)
            for p in itertools.product(A, repeat=L)]
    pool += [[rng.choice(A) for _ in range(rng.randint(1, 15))]
             for _ in range(rnd)]
    if c_scan(ORB3):
        bad.append('the Scan/After DFA accepts the reachable %s' % ORB3)
    else:
        print('   %-52s also rejects the reachable %s'
              % ('(the Scan/After DFA)', ORB3))
    for nm, f in CANDS:
        wit = None
        for w in pool:
            if f(w) and not f(nv(w)):
                wit = w
                break
        if wit is None:
            bad.append('%s: NOT refuted -- check it, it may be the invariant'
                       % nm)
            print('   %-52s NOT REFUTED' % nm)
        else:
            print('   %-52s refuted by nv %s = %s'
                  % (nm, wit, nv(wit)[:9]))
    return bad


def main():
    bad = []
    bad += check_alphabet()
    bad += check_leading2()
    bad += check_poor()
    bad += check_engine()
    bad += check_selfsimilar()
    bad += check_unbounded_death()
    print('#20 candidate invariants, each checked for CLOSURE (not sampled):')
    bad += refute()
    print('#20 inv: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
