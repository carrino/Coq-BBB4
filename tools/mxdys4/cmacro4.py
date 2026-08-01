#!/usr/bin/env python3
"""UNTRUSTED: M4's macro system in CCONF coordinates, differentially
validated against the raw simulator.

M4 = 1RB1LD_1LC1RA_0RB0LC_0RA0LD keeps its LEFT half-tape a bare unary run
for its whole orbit (docs/WAVE36_MXDYS_FOUR section 2b), so the whole
configuration is (StA, (rep [S1] p ++ S0 :: Y, s, r)) -- [Y] a tail the run
never reaches, [r] the (arbitrary) right half-tape carrying the counter.
Five rules, exact step counts:

  (1)  s=S0, chd r=S1        : (p, S0, r)     -> (p+2, chd r1, ctl r1)   2
                                                 r1 = ctl r
  (2)  s=S0, chd r=S0, p=m+1 : (m+1, S0, r)   -> (1, S0, 0^m ++ 1::ctl r) m+8
  (2') s=S0, chd r=S0, p=0   : (0, S0, r)     -> (1, S1, ctl r)           7
  (3)  s=S1, p=m+1           : (m+1, S1, r)   -> (0, S0, 0^m ++ 1::r)     m+3
  (3') s=S1, p=0             : (0, S1, r)     -> (0, S1, r)               2

[StD] is visited by rules 3 and 3' and by no other, so the liveness of
[StD] is exactly "the head reads S1 in state A infinitely often".

Usage:  python3 tools/mxdys4/cmacro4.py [nmacro]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Sim                                                # noqa: E402

CODE = '1RB1LD_1LC1RA_0RB0LC_0RA0LD'


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def rule(p, s, r):
    if s == 0:
        if chd(r) == 1:
            r1 = ctl(r)
            return ('1', 2, p + 2, chd(r1), ctl(r1))
        if p == 0:
            return ("2'", 7, 1, 1, ctl(r))
        m = p - 1
        return ('2', m + 8, 1, 0, [0] * m + [1] + ctl(r))
    if p == 0:
        return ("3'", 2, 0, 1, list(r))
    m = p - 1
    return ('3', m + 3, 0, 0, [0] * m + [1] + list(r))


def val(r):
    v = 0
    for b in reversed(r):
        v = 2 * v + b
    return v


def mu(p, s, r):
    return 2 ** p * (2 * val(r) + s + 1)


def width(p, r):
    return p + 1 + len(r)


def macro_run(n, p=0, s=0, r=None, t=0):
    r = [] if r is None else r
    out = []
    for _ in range(n):
        nm, c, p, s, r = rule(p, s, r)
        t += c
        out.append((t, nm, p, s, list(r)))
    return out


def raw_cconf(t):
    sm = Sim(CODE)
    for _ in range(t):
        sm.step()
    ks = [k for k, v in sm.tape.items() if v]
    lo = min(ks + [sm.pos])
    hi = max(ks + [sm.pos])
    q = sm.pos
    left = [sm.tape[j] for j in range(q - 1, lo - 1, -1)]
    right = [sm.tape[j] for j in range(q + 1, hi + 1)]
    while right and right[-1] == 0:
        right.pop()
    p = 0
    while p < len(left) and left[p] == 1:
        p += 1
    ok = (sm.st == 'A') and all(x == 0 for x in left[p:])
    return p, sm.tape[q], right, ok


def norm(r):
    r = list(r)
    while r and r[-1] == 0:
        r.pop()
    return r


def validate(n):
    bad = 0
    for (t, nm, p, s, r) in macro_run(n):
        rp, rs, rr, ok = raw_cconf(t)
        if not ok or rp != p or rs != s or rr != norm(r):
            bad += 1
            if bad < 6:
                print('MISMATCH t=%d rule=%s macro=(%d,%d,%s) raw=(%d,%d,%s,%s)'
                      % (t, nm, p, s, r, rp, rs, rr, ok))
    print('cconf macro rules: %d / %d matched (%d bad)' % (n - bad, n, bad))
    return bad


def deltas(n):
    """mu strictly increases on 1 / 2 / 2' and w is preserved -- except when
    the head walks into FRESH blank tape on the right, which is the only
    place w can grow."""
    p, s, r = 0, 0, []
    bad = 0
    grow = 0
    for _ in range(n):
        nm, c, p2, s2, r2 = rule(p, s, r)
        m0, m1 = mu(p, s, r), mu(p2, s2, r2)
        w0, w1 = width(p, r), width(p2, r2)
        if nm in ('1', '2', "2'") and m1 <= m0:
            bad += 1
            if bad < 6:
                print('MU rule=%s %d -> %d' % (nm, m0, m1))
        if w1 != w0:
            grow += 1
            if grow < 6:
                print('WIDEN rule=%s w %d -> %d  p=%d r=%s' % (nm, w0, w1, p, r))
        p, s, r = p2, s2, r2
    print('mu/width: %d mu violations, %d widenings over %d macro steps'
          % (bad, grow, n))
    return bad


def inv(n):
    """Candidate invariant, the mirror of M1's: [last r] = S1, [len r] and
    [p] of matching parity.  Reported per rule so the phases show up."""
    p, s, r = 0, 0, []
    stats = {}
    for _ in range(n):
        nm, c, p, s, r = rule(p, s, r)
        key = (nm, len(r) % 2, p % 2, (r[-1] if r else 0))
        stats[key] = stats.get(key, 0) + 1
    for k in sorted(stats):
        print('  rule=%-3s |r|%%2=%d p%%2=%d last=%d   %d' % (k + (stats[k],)))


# --- the predicate the Coq proof actually carries -------------------------
# G = IO \/ IE \/ Z0 \/ Z1, closed under ONE macro rule; StD is hit from
# every member of it.  Unlike M1's, this one depends on the head symbol:
# the two blank-tape states are reachable at one parity of [p] each.
# (theories/Machines/Mxdys4/NGX_1RB1LD_...v)

def IO(p, r):
    return p % 2 == 1 and len(r) % 2 == 0 and bool(r) and r[-1] == 1


def IE(p, r):
    return p % 2 == 0 and len(r) % 2 == 1 and bool(r) and r[-1] == 1


def G(p, s, r):
    return (IO(p, r) or IE(p, r)
            or (r == [] and p % 2 == 0 and s == 0)
            or (r == [] and p % 2 == 1 and s == 1))


def hitsD(p, s, r, limit=20000):
    """rules 3 and 3' -- the only two places StD occurs."""
    for _ in range(limit):
        nm, c, p, s, r = rule(p, s, r)
        if nm.startswith('3'):
            return True
    return False


def check_G(maxp=7, maxr=12):
    """Exhaustive over p <= maxp, |r| <= maxr: G is closed under one macro
    rule, and StD is hit from every member of G.  The controls are the
    NON-members, where both may fail -- and do."""
    import itertools
    closed_bad = hit_bad = members = 0
    ctrl_open = ctrl_nohit = ctrl = 0
    for n in range(maxr + 1):
        for bits in itertools.product((0, 1), repeat=n):
            r = list(bits)
            for p in range(maxp + 1):
                for s in (0, 1):
                    _, _, p2, s2, r2 = rule(p, s, r)
                    if G(p, s, r):
                        members += 1
                        if not G(p2, s2, r2):
                            closed_bad += 1
                            if closed_bad < 4:
                                print('  NOT CLOSED: (%d,%d,%s) -> (%d,%d,%s)'
                                      % (p, s, r, p2, s2, r2))
                        if not hitsD(p, s, r):
                            hit_bad += 1
                    else:
                        ctrl += 1
                        ctrl_open += (not G(p2, s2, r2))
                        ctrl_nohit += (not hitsD(p, s, r))
    print('G closure : %d members, %d not closed, %d never reach StD'
          % (members, closed_bad, hit_bad))
    print('  control : %d non-members, %d leave G, %d never reach StD '
          '(both MUST be nonzero)' % (ctrl, ctrl_open, ctrl_nohit))
    return closed_bad + hit_bad


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    validate(n)
    deltas(4000)
    print('\n=== post-rule parity census (4000 macro steps) ===')
    inv(4000)
    print()
    check_G()
    print('\n=== cconf macro trace ===')
    for (t, nm, p, s, r) in macro_run(40):
        print('%-3s t=%-7d p=%-3d |r|=%-3d w=%-3d s=%d mu=%-10d r=%s'
              % (nm, t, p, len(r), width(p, r), s, mu(p, s, r),
                 ''.join(map(str, r))))
