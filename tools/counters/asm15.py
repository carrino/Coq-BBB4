#!/usr/bin/env python3
"""Step 0 for boarding wave4 #15: replay the lap using ONLY the verified
gadgets, symbolically, and diff it against the real machine.

`lap15.py` verifies each gadget in isolation.  That is not enough to write
the Coq: the LAP is a composition, and the composition is where the block
parities have to line up.  This file composes the gadgets as pure list
operations -- it never calls `cstep` to build a state -- and then checks the
result against `probe15`'s raw simulator, step count and configuration.

If this is green for every p, the Coq lap proof is a transcription: the
gadget sequence printed by `trace(p)` IS the proof script, and the regular
structure in it is the induction.

  ruleA    (StC,([],S0,      S1::S0::S1::R)) -10-> (StC,([],S0,S1::S1::S0::S1::S1::R))
  entry5   (StC,([],S0,      S1::S1::S0::R))  -5-> (StC,([S0;S0;S1;S1],S0,R))
  out6     (StC,(S0::L,S0,   S1::S1::S1::R))  -6-> (StC,(S0::S1::S1::L,S0,S1::R))
  carry5   (StC,(S0::L,S0,   S1::S1::S0::R))  -5-> (StC,(S0::S0::S1::S1::L,S0,R))
  deposit  (StC,(S0::L,S0,   S1::S0::R))    -5+k+1-> ...   (a SWEEP, not a window)
  ret1     (StC,(S1::L,S1,R))                 -1-> (StC,(L,S1,S1::R))
  cross7   (StC,(S0::S1::S1::L,S1,R))         -7-> (StC,(L,S1,S0::S1::S1::R))
  exit1    (StC,([],S1,R))                    -1-> (StC,([],S0,S1::R))

The deposit is the one piece that is not a fixed window: it is
`cD . dR . dR . dA . aB . bB^k . bC`, and the `bB^k` walk-back runs over the
laid 1s until it meets a 0.  Here it is built from the single-step joints,
each of which IS verified uniform, with k discovered by the walk.

UNTRUSTED, like everything under tools/.  Usage: `python3 asm15.py [maxp]`.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe15 import cstep, chd, ctl, A, B, C, D, S0, S1
from lap15 import venc, pos15, blocks

NM = 'ABCD'


def anchor(p):
    """Cf15 p, built from the structural recursion -- not from the simulator."""
    lead = 1 + (p % 2)
    R = [S1] * lead + [S0]
    for x in venc(p):
        R += [S1] * x + [S0]
    return (C, [], S0, R)


# -- the single-step joints (the transition table, each a reflexivity in Coq)
def cD(s): q, L, h, R = s; return (D, ctl(L), chd(L), [S0] + R)
def dR(s): q, L, h, R = s; return (D, [S1] + L, chd(R), ctl(R))
def dA(s): q, L, h, R = s; return (A, [S0] + L, chd(R), ctl(R))
def aB(s): q, L, h, R = s; return (B, [S1] + L, chd(R), ctl(R))
def bB(s): q, L, h, R = s; return (B, ctl(L), chd(L), [S1] + R)
def bC(s): q, L, h, R = s; return (C, ctl(L), chd(L), [S0] + R)


def deposit(s):
    """cD . dR . dR . dA . aB . bB^k . bC -- John's 'moves it 1 left and
    bounces'.  Returns (newstate, nsteps, k)."""
    t = bC(  # the final B0
        None) if False else None
    u = s
    for f in (cD, dR, dR, dA, aB):
        u = f(u)
    k = 0
    while u[3] is not None and u[2] == S1:      # head is a 1: keep walking back
        u = bB(u)
        k += 1
    u = bC(u)
    return u, 5 + k + 1, k


GADGETS = [
    ('ruleA', lambda s: s[0] == C and s[1] == [] and s[2] == S0 and s[3][:3] == [S1, S0, S1],
     lambda s: ((C, [], S0, [S1, S1, S0, S1, S1] + s[3][3:]), 10, None)),
    ('entry5', lambda s: s[0] == C and s[1] == [] and s[2] == S0 and s[3][:3] == [S1, S1, S0],
     lambda s: ((C, [S0, S0, S1, S1], S0, s[3][3:]), 5, None)),
    ('out6', lambda s: s[0] == C and s[1][:1] == [S0] and s[2] == S0 and s[3][:3] == [S1, S1, S1],
     lambda s: ((C, [S0, S1, S1] + s[1][1:], S0, [S1] + s[3][3:]), 6, None)),
    ('carry5', lambda s: s[0] == C and s[1][:1] == [S0] and s[2] == S0 and s[3][:3] == [S1, S1, S0],
     lambda s: ((C, [S0, S0, S1, S1] + s[1][1:], S0, s[3][3:]), 5, None)),
    ('deposit', lambda s: s[0] == C and s[1][:1] == [S0] and s[2] == S0 and s[3][:2] == [S1, S0],
     deposit),
    ('cross7', lambda s: s[0] == C and s[1][:3] == [S0, S1, S1] and s[2] == S1,
     lambda s: ((C, s[1][3:], S1, [S0, S1, S1] + s[3]), 7, None)),
    ('ret1', lambda s: s[0] == C and s[1][:1] == [S1] and s[2] == S1,
     lambda s: ((C, s[1][1:], S1, [S1] + s[3]), 1, None)),
    ('exit1', lambda s: s[0] == C and s[1] == [] and s[2] == S1,
     lambda s: ((C, [], S0, [S1] + s[3]), 1, None)),
]


def is_anchor(s):
    return s[0] == C and s[1] == [] and s[2] == S0 and s[3] and s[3][0] == S1


def replay(p, cap=4000):
    """Compose gadgets from Cf15 p until the next anchor.  Pure list ops."""
    s = anchor(p)
    seq, total = [], 0
    for _ in range(cap):
        hit = None
        for (nm, m, f) in GADGETS:
            if m(s):
                hit = (nm, f)
                break
        if hit is None:
            return None, seq, total, 'stuck at %s %s [%s] %s' % (
                NM[s[0]], s[1][:6], s[2], s[3][:6])
        s2, n, k = hit[1](s)
        seq.append(hit[0] if k is None else '%s(k=%d)' % (hit[0], k))
        total += n
        s = s2
        if is_anchor(s) and seq[-1] not in ('entry5',):
            return s, seq, total, None
    return None, seq, total, 'cap'


def real(p, cap=200000):
    """The same lap, from the raw simulator."""
    lead = 1 + (p % 2)
    R = [S1] * lead + [S0]
    for x in venc(p):
        R += [S1] * x + [S0]
    c = (C, ([], S0, R))
    for t in range(1, cap):
        c = cstep(c)
        if c is None:
            return None, None
        q, (L, h, RR) = c
        if q == C and L == [] and h == S0 and RR and RR[0] == S1:
            return t, (q, L, h, RR)
    return None, None


def compress(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' . '.join('%s^%d' % (a, b) if b > 1 else a for a, b in out)


def main():
    maxp = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    bad = []
    for p in range(2, maxp):
        got, seq, n, err = replay(p)
        t, rc = real(p)
        if err:
            bad.append('p=%d: %s' % (p, err))
            continue
        want = anchor(p + 1)
        want = (want[0], want[1], want[2], want[3])
        if n != t:
            bad.append('p=%d: %d steps, machine says %s' % (p, n, t))
        elif (got[0], got[1], got[2], got[3]) != want:
            bad.append('p=%d: config mismatch\n   got  %s\n   want %s' % (p, got, want))
        if len(bad) > 4:
            break
    print('#15 symbolic assembly, p = 2 .. %d' % (maxp - 1))
    for b in bad[:5]:
        print('  FAIL %s' % b)
    print('  %s' % ('OK -- the lap IS a composition of the verified gadgets'
                    if not bad else '%d FAILURES' % len(bad)))
    if not bad:
        print()
        print('  the gadget sequence (this is the Coq proof script):')
        for p in (2, 3, 4, 5, 6, 7, 8, 15, 16, 31, 32):
            _, seq, n, _ = replay(p)
            print('   p=%-4d %-4s n=%-4d %s' % (p, 'even' if p % 2 == 0 else 'odd', n, compress(seq)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
