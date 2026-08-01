#!/usr/bin/env python3
"""UNTRUSTED: M1's macro system in CCONF coordinates (the form the Coq
proof is written in), differentially validated against the raw simulator.

The frame-based rules of docs/WAVE36_MXDYS_FOUR section 2a are restated on
[cconf] = (StA, (l, s, rep [S1] R ++ S0 :: Z)) with

  l  the left half-tape, NEAREST CELL FIRST (so [length l] is the head
     position [p] and [last l] is the frame's cell 0),
  s  the head symbol,
  R  the length of the unary run to the right of the head,
  Z  a tail the run never touches (it is invariant under all four rules --
     that is what makes the rules composable without a trailing-blank
     mismatch).

Rules, with exact step counts:

  (1) s=S0, R=k+2 : (l, S0, k+2) -> (0^k ++ S1::l, S0, 1)      k+5 steps
  (2a) s=S0, R=0  : (l, S0, 0)   -> (l, S1, 0)                 4 steps
  (2b) s=S0, R=1  : (l, S0, 1)   -> (l, S1, 1)                 4 steps
  (4) s=S1, l=S0::l1 : -> (ctl l1, chd l1, R+2)                2 steps
  (5) s=S1, l=S1::L  : -> (0^R ++ S1::L, S0, 0)                R+4 steps

Usage:  python3 tools/mxdys4/cmacro1.py [nmacro]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Sim                                                # noqa: E402

CODE = '1RB1LC_0LC0RB_1LA1RD_0LA0RD'


def rule(l, s, R):
    """-> (name, cost, l', s', R') on the cconf triple.  [l] is a list of
    0/1, nearest cell first."""
    if s == 0:
        if R >= 2:
            k = R - 2
            return ('1', k + 5, [0] * k + [1] + l, 0, 1)
        return ('2', 4, l[:], 1, R)
    # s == 1
    if (l[0] if l else 0) == 0:
        l1 = l[1:]
        return ('4', 2, l1[1:], (l1[0] if l1 else 0), R + 2)
    return ('5', R + 4, [0] * R + l, 0, 0)


def val(l):
    """[vall]: the left half-tape as a binary number, nearest cell least
    significant."""
    v = 0
    for b in reversed(l):
        v = 2 * v + b
    return v


def mu(l, s, R):
    return 2 ** R * (2 * val(l) + s + 1)


def width(l, R):
    return len(l) + 1 + R


def macro_run(n, l=None, s=1, R=0, t=4):
    l = [] if l is None else l
    out = []
    for _ in range(n):
        nm, c, l, s, R = rule(l, s, R)
        t += c
        out.append((t, nm, list(l), s, R))
    return out


def raw_cconf(t):
    """The raw simulator's configuration at time [t], as (l, s, R, ok) with
    [ok] false when the right half-tape is not 1^R followed by blanks."""
    sm = Sim(CODE)
    for _ in range(t):
        sm.step()
    ks = [k for k, v in sm.tape.items() if v]
    lo = min(ks + [sm.pos])
    hi = max(ks + [sm.pos])
    p = sm.pos
    left = [sm.tape[j] for j in range(p - 1, lo - 1, -1)]
    while left and left[-1] == 0:
        left.pop()
    right = [sm.tape[j] for j in range(p + 1, hi + 1)]
    R = 0
    while R < len(right) and right[R] == 1:
        R += 1
    ok = (sm.st == 'A') and all(x == 0 for x in right[R:])
    return left, sm.tape[p], R, ok


def validate(n):
    bad = 0
    for (t, nm, l, s, R) in macro_run(n):
        rl, rs, rR, ok = raw_cconf(t)
        if not ok or rl != l or rs != s or rR != R:
            bad += 1
            if bad < 6:
                print('MISMATCH t=%d rule=%s macro=(%s,%d,%d) raw=(%s,%d,%d,%s)'
                      % (t, nm, l, s, R, rl, rs, rR, ok))
    print('cconf macro rules: %d / %d matched (%d bad)' % (n - bad, n, bad))
    return bad


def deltas(n):
    """Check section 4a's four exact deltas and the width preservation."""
    want = {'1': lambda l, s, R: 2,
            '2': lambda l, s, R: 2 ** R,
            '4': lambda l, s, R: 2 ** (R + 1),
            '5': lambda l, s, R: -(2 ** (R + 1) - 1)}
    l, s, R = [], 1, 0
    bad = 0
    for _ in range(n):
        nm, c, l2, s2, R2 = rule(l, s, R)
        d = mu(l2, s2, R2) - mu(l, s, R)
        if d != want[nm](l, s, R):
            bad += 1
            if bad < 6:
                print('DELTA rule=%s got=%d want=%d' % (nm, d, want[nm](l, s, R)))
        if nm != '4' or l:                        # rule 4 at l=[] widens
            if width(l2, R2) != width(l, R) and not (nm == '4' and len(l) <= 1):
                bad += 1
                if bad < 6:
                    print('WIDTH rule=%s %d -> %d  l=%s R=%d'
                          % (nm, width(l, R), width(l2, R2), l, R))
        l, s, R = l2, s2, R2
    print('deltas + width: %d bad over %d macro steps' % (bad, n))
    return bad


def invariant(n):
    """The odd-phase invariant of section 4: after every rule 1, [length l]
    is odd, [R] is odd and [last l] = S1, and it survives 1/2/4."""
    l, s, R = [], 1, 0
    armed = False
    bad = 0
    for i in range(n):
        nm, c, l2, s2, R2 = rule(l, s, R)
        if armed and nm in '124':
            if not (len(l2) % 2 == 1 and R2 % 2 == 1 and l2 and l2[-1] == 1):
                bad += 1
                if bad < 6:
                    print('INV broken after rule %s: l=%s R=%d' % (nm, l2, R2))
        if nm == '1':
            armed = True
        if nm == '5':
            armed = False
        l, s, R = l2, s2, R2
    print('odd-phase invariant: %d violations over %d macro steps' % (bad, n))
    return bad


# --- the predicate the Coq proof actually carries -------------------------
# G = IO \/ IE \/ IZ, closed under ONE macro rule; StD is hit from every
# member of it.  (theories/Machines/Mxdys4/NGX_1RB1LC_...v)

def IO(l, R):
    return len(l) % 2 == 1 and R % 2 == 1 and bool(l) and l[-1] == 1


def IE(l, R):
    return len(l) % 2 == 0 and R % 2 == 0 and bool(l) and l[-1] == 1


def IZ(l, R):
    return l == [] and R % 2 == 0


def G(l, R):
    return IO(l, R) or IE(l, R) or IZ(l, R)


def hitsD(l, s, R, limit=20000):
    """rule 5, or rule 2 at R = 0 -- the two places StD occurs.  The limit
    has to be generous: the wait is the exponential this row is about, and
    ([0,1]*6, S1, 6) alone needs over 2000 macro steps."""
    for _ in range(limit):
        nm, c, l, s, R = rule(l, s, R)
        if nm == '5' or (nm == '2' and R == 0):
            return True
    return False


def check_G(maxl=12, maxR=7):
    """Exhaustive over |l| <= maxl, R <= maxR: G is closed under one macro
    rule, and StD is hit from every member of G.  The controls are the
    NON-members, where both may fail -- and do."""
    import itertools
    closed_bad = hit_bad = members = 0
    ctrl_open = ctrl_nohit = ctrl = 0
    for n in range(maxl + 1):
        for bits in itertools.product((0, 1), repeat=n):
            l = list(bits)
            for R in range(maxR + 1):
                for s in (0, 1):
                    _, _, l2, s2, R2 = rule(l, s, R)
                    if G(l, R):
                        members += 1
                        if not G(l2, R2):
                            closed_bad += 1
                            if closed_bad < 4:
                                print('  NOT CLOSED: (%s,%d,%d) -> (%s,%d,%d)'
                                      % (l, s, R, l2, s2, R2))
                        if not hitsD(l, s, R):
                            hit_bad += 1
                    else:
                        ctrl += 1
                        ctrl_open += (not G(l2, R2))
                        ctrl_nohit += (not hitsD(l, s, R))
    print('G closure : %d members, %d not closed, %d never reach StD'
          % (members, closed_bad, hit_bad))
    print('  control : %d non-members, %d leave G, %d never reach StD '
          '(both MUST be nonzero)' % (ctrl, ctrl_open, ctrl_nohit))
    return closed_bad + hit_bad


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    validate(n)
    deltas(4000)
    invariant(4000)
    check_G()
    print('\n=== cconf macro trace ===')
    for (t, nm, l, s, R) in macro_run(40):
        print('%-3s t=%-7d p=%-3d R=%-3d w=%-3d s=%d mu=%-8d l=%s'
              % (nm, t, len(l), R, width(l, R), s, mu(l, s, R),
                 ''.join(map(str, l))))
