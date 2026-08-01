#!/usr/bin/env python3
"""UNTRUSTED ORACLE for the LAZY fibonacci representative.

`tools/counters/fibform.py` measures WHAT the six surviving fibonacci core
rows count in: the kernel's own numeration (`LadderFam.fibw` = 1,1,2,3,5,8,
`fam_lim k = S (fibsum k)`, widths spanning `[fibw k .. fibsum k]`), standing
on the OTHER representative -- LSB-first, no two adjacent zeros -- where
`LadderFam.fibdec` and `LadderCheck.fibokb` pick the greedy one.

This file is the oracle for the class laws that representative satisfies, in
the tradition `tools/ladder/fibmem.py` set for `(Fib, 1)` and `gray2check.py`
for `(Gray, 2)`: state nothing in Coq that the Python has not checked against
the machine's own orbit.  What it checks, over every interior step of every
one of the six rows:

  INTERIOR, two classes, split on the PARITY of the low run of ones --

    E   (1,1)^m ++ [0]        ++ rest  ->  (1,0)^m ++ [1] ++ rest
    O   [1] ++ (1,1)^m ++ [0] ++ rest  ->  [1] ++ (1,0)^m ++ [1] ++ rest

  FILL, the top of a width, likewise two, and the width's parity is the
  PHASE (`Fill.f_to` already alternates a phase, so no field is needed) --

    E   (1,1)^m                ->  (1,0)^m ++ [1]           (k = 2m   -> k+1)
    O   [1] ++ (1,1)^m         ->  [1] ++ (1,0)^m ++ [1]    (k = 2m+1 -> k+2)

The point of writing them this way is what it costs in the kernel: NOTHING
about the numeration moves -- not `fibw`, not `fibsum`, not `fam_lim`, not
`fibval` -- and the classes need exactly ONE widening, the run unit of
`Class` (`cs_t`) and of `Fill` (`f_mid`) becoming a digit WORD rather than a
single digit.  There is no stride: the LHS run `1^n` is `(1,1)^m` at the same
exponent the RHS run `(1,0)^m` uses.  The cell side already speaks word runs
(`flat_map_repeat` lands on `rep (dig F t) n`, and `rep` takes a word), so
the widening is on the DIGIT-string side only.

Nothing here carries proof weight.
"""

import argparse
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/counters')

from fibform import ROWS, fibsum, fibval, fibw, no_adj_zero  # noqa: E402
from nestscan import run                                      # noqa: E402


def orbit(code, T, q0, h0, side, other):
    """value -> the machine's own digit string at that value."""
    seen = {}
    for (q, l, h, r) in run(code, T):
        if q != q0 or h != h0:
            continue
        w, o = (r, l) if side == 'R' else (l, r)
        if len(o) != other or not w:
            continue
        seen.setdefault(fibval(w), tuple(w))
    return seen


def best_anchor(code, T, tmax=3):
    """The anchor with the longest run of consecutive `fibval`s -- the same
    anchor space `fib_anchor.py` scans, restricted to a fixed far-side
    width."""
    from collections import defaultdict
    fams = defaultdict(list)
    for (q, l, h, r) in run(code, T):
        for t in range(tmax + 1):
            if len(r) == t:
                fams[(q, h, 'L', t)].append(tuple(l))
            if len(l) == t:
                fams[(q, h, 'R', t)].append(tuple(r))
    best = None
    for key, ws in fams.items():
        ws = ws[:4000]
        if len(ws) < 50:
            continue
        vs = [None if not w else fibval(w) for w in ws]
        n = cur = 0
        for i, v in enumerate(vs):
            cur = cur + 1 if (cur and vs[i - 1] is not None
                              and v is not None and v == vs[i - 1] + 1) else 1
            n = max(n, cur)
        if best is None or n > best[0]:
            best = (n, key)
    return best


# --------------------------------------------------------------- the laws

def alt(n):
    """The alternating string of length [n], LSB-first, top digit 1:
    `(1,0)^m 1` at odd [n] and `1 (1,0)^m 1` at even [n]."""
    return tuple((1 if i % 2 == 0 else 0) if n % 2 else
                 (1 if i == 0 or i % 2 else 0) for i in range(n))


def cls_lhs(par, m, rest):
    """[par] 0 = E, 1 = O."""
    return tuple([1] * par + [1, 1] * m + [0]) + rest


def cls_rhs(par, m, rest):
    return tuple([1] * par + [1, 0] * m + [1]) + rest


def fill_lhs(par, m):
    return tuple([1] * par + [1, 1] * m)


def fill_rhs(par, m):
    return tuple([1] * par + [1, 0] * m + [1])


def split(ds):
    """Decompose a member into (class parity, m, rest), or None if it is the
    top of its width -- the coverage claim, as a function."""
    n = 0
    while n < len(ds) and ds[n] == 1:
        n += 1
    if n == len(ds):
        return None                       # the top: 1^k
    assert ds[n] == 0
    return (n % 2, n // 2, tuple(ds[n + 1:]))


def check(code, T=200000, verbose=False):
    b = best_anchor(code, T)
    if b is None:
        return {'spec': code, 'ok': False, 'why': 'no anchor'}
    n, (q0, h0, side, other) = b
    seen = orbit(code, T, q0, h0, side, other)
    vs = sorted(seen)
    rec = {'spec': code,
           'anchor': '%s h=S%d %s |other|=%d' % (q0, h0, side, other),
           'consecutive': n, 'values': len(seen),
           'interior': 0, 'fill': 0, 'member': 0,
           'bad_interior': [], 'bad_fill': [], 'bad_member': [],
           'bad_split': [], 'bad_value': []}
    for v in vs:
        ds = seen[v]
        if no_adj_zero(ds):
            rec['member'] += 1
        elif len(rec['bad_member']) < 4:
            rec['bad_member'].append((v, list(ds)))
        k = len(ds)
        sp = split(ds)
        if sp is None:
            # the TOP of a width: its value must be `fibsum k` and its
            # string `1^k`, which is what `fam_top` asks of the fill
            if v != fibsum(k) or ds != tuple([1] * k):
                rec['bad_split'].append((v, list(ds)))
        else:
            par, m, rest = sp
            if cls_lhs(par, m, rest) != ds:
                rec['bad_split'].append((v, list(ds)))
        if v + 1 not in seen:
            continue
        nxt = seen[v + 1]
        if sp is None:
            par, m = k % 2, k // 2
            got = fill_rhs(par, m)
            if got == nxt and fill_lhs(par, m) == ds:
                rec['fill'] += 1
            else:
                rec['bad_fill'].append((v, list(ds), list(nxt), list(got)))
        else:
            par, m, rest = sp
            got = cls_rhs(par, m, rest)
            if got == nxt:
                rec['interior'] += 1
            else:
                rec['bad_interior'].append((v, list(ds), list(nxt), list(got)))
        # the arithmetic the class law claims, independently of the shape
        if fibval(nxt) != fibval(ds) + 1:
            rec['bad_value'].append(v)
    rec['ok'] = not (rec['bad_interior'] or rec['bad_fill']
                     or rec['bad_member'] or rec['bad_split']
                     or rec['bad_value'])
    return rec


def selftest():
    """Corruption controls: each mutation MUST make the check fail, or the
    check is not checking anything (the tradition of `theories/Tests/`)."""
    fails = []
    # 1. the alternating RHS is not a run of ZEROS
    for m in range(1, 6):
        if cls_rhs(0, m, ()) == tuple([0] * 2 * m + [1]):
            fails.append('cls_rhs collapsed to a zero run at m=%d' % m)
    # 2. the two parities are genuinely different classes
    for m in range(4):
        if cls_lhs(0, m, ()) == cls_lhs(1, m, ()):
            fails.append('the parities coincide at m=%d' % m)
    # 3. every class instance really is +1 in the numeration
    for par in (0, 1):
        for m in range(6):
            for rest in ((), (1,), (0, 1), (1, 1), (1, 0, 1)):
                a, b = cls_lhs(par, m, rest), cls_rhs(par, m, rest)
                if fibval(b) != fibval(a) + 1:
                    fails.append('class (%d,%d,%s) is not +1' % (par, m, rest))
                if len(a) != len(b):
                    fails.append('class (%d,%d,%s) changes width' % (par, m, rest))
                if not no_adj_zero(b):
                    fails.append('class (%d,%d,%s) leaves the family'
                                 % (par, m, rest))
    # 4. and the fill: it widens by one and lands on the width's floor
    for par in (0, 1):
        for m in range(6):
            k = 2 * m + par
            if k == 0:
                continue
            a, b = fill_lhs(par, m), fill_rhs(par, m)
            if fibval(a) != fibsum(k):
                fails.append('fill lhs at k=%d is not the top' % k)
            if fibval(b) != fibsum(k) + 1 or fibval(b) != fibw(k + 1):
                fails.append('fill rhs at k=%d is not the next floor' % k)
            if len(b) != k + 1 or not no_adj_zero(b):
                fails.append('fill rhs at k=%d is not a member of k+1' % k)
    # 5. `alt` agrees with the closed forms.  The fill leaves width [k] for
    # width [k+1], so it is [alt (k+1)] that the two parities spell.
    for k in range(1, 12):
        if alt(k + 1) != fill_rhs(k % 2, k // 2):
            fails.append('alt disagrees with fill_rhs at k=%d' % k)
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--steps', type=int, default=200000)
    ap.add_argument('--selftest', action='store_true')
    a = ap.parse_args()
    if a.selftest:
        f = selftest()
        print('SELFTEST: %s' % ('OK' if not f else 'FAILED'))
        for x in f:
            print('  ' + x)
        return 0 if not f else 1
    bad = 0
    for code in ([a.spec] if a.spec else ROWS):
        r = check(code, a.steps)
        print('%-30s %s  consec=%d values=%d  interior=%d fill=%d member=%d  %s'
              % (code, r.get('anchor', '-'), r.get('consecutive', 0),
                 r.get('values', 0), r.get('interior', 0), r.get('fill', 0),
                 r.get('member', 0), 'OK' if r['ok'] else 'FAILED'))
        for key in ('bad_member', 'bad_split', 'bad_interior', 'bad_fill',
                    'bad_value'):
            if r.get(key):
                bad += 1
                print('    %s: %d, first %s' % (key, len(r[key]), r[key][:2]))
        sys.stdout.flush()
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
