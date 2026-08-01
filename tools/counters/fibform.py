#!/usr/bin/env python3
"""UNTRUSTED.  Which REPRESENTATIVE does a fibonacci row stand on?

`fib_anchor.py` says the six surviving fibonacci core rows read at weights
`F(1,1) = 1,1,2,3,5,8` and `valfam.py --numeration` says `1,2,3,5,8,13`.
LADDER_PLAN 4s read the second as a different numeration (Zeckendorf) and
made building it the next session's task.  It is not a different numeration.
The two readings are the SAME anchor one cell apart: the cell nearest the
head is a constant `1` at every anchor visit, `valfam` strips it into
`fm_pre` (its `p = 1`), and `1,2,3,5,8,13` is `1,1,2,3,5,8` with that
constant's weight removed.  `fit_weights` cannot do otherwise -- a column
that never varies contributes nothing to the enumeration-order equations, so
its weight comes back undetermined and the whole fit is dropped.

So the question is not the weights.  It is the REPRESENTATIVE: `fibw` is
redundant (`fibw 0 = fibw 1 = 1`), and `LadderFam.fibdec` -- the kernel's
decoder -- picks a different member of each value's class than these machines
spell.  This tool measures both halves against the raw simulator:

  * the ARITHMETIC: is the full anchor word's `fibval` exactly the anchor
    visit index, and does width `k` span exactly `[fibw (k-1) .. fibsum k]`
    with `fibonacci(k)` strings in it?  That is the kernel's `fam_lim`.
  * the FORM: does the machine's string equal `fibdec k false v`, and if not,
    which regular language is it?  Two candidates are checked, both LSB-first
    (index 0 nearest the head): NO TWO ADJACENT ZEROS, which is the greedy
    representative, and the kernel's own automaton.

Nothing here carries proof weight.
"""

import argparse
import sys
from collections import defaultdict

from nestscan import run

ROWS = [
    '1RB---_0LC1RD_1LB1RC_1LB0RD',
    '1RB---_0LC1RD_1LB1RD_1LB0RD',
    '1RB---_1LC0RB_0LD1RB_1LC1RB',
    '1RB---_1LC0RB_0LD1RB_1LC1RD',
    '1RB---_1LC1RB_0LB1RD_1LC0RD',
    '1RB---_1LC1RD_0LB1RD_1LC0RD',
]


def fibw(i):
    a, b = 1, 1
    for _ in range(i):
        a, b = b, a + b
    return a


def fibsum(k):
    return sum(fibw(i) for i in range(k))


def fibval(ds):
    return sum(d * fibw(i) for i, d in enumerate(ds))


def fibdec(k, o, v):
    """`LadderFam.fibdec`, transcribed.  LSB-first output, top digit last."""
    if k == 0:
        return []
    kp = k - 1
    if o or fibw(k) <= v:
        return fibdec(kp, not o, v - fibw(kp)) + [1]
    return fibdec(kp, False, v) + [0]


def no_adj_zero(ds):
    """LSB-first: no two adjacent 0s, and the top digit is 1."""
    return bool(ds) and ds[-1] == 1 and all(
        not (ds[i] == 0 and ds[i + 1] == 0) for i in range(len(ds) - 1))


def kernel_member(ds):
    """The automaton `LadderFam` describes for `fibdec`: read MSB-first, a 1
    must be followed by a 1, except in the run that reaches index 0."""
    o = False
    for d in reversed(ds):
        if o:
            if d != 1:
                return False
            o = False
        else:
            o = (d == 1)
    return True


def anchors(code, T, tmax=3):
    """Every (state, head symbol, side, |far side|) family, far side fixed
    width -- `fib_anchor.scan`'s anchor space."""
    fams = defaultdict(list)
    for (q, l, h, r) in run(code, T):
        for t in range(tmax + 1):
            if len(r) == t:
                fams[(q, h, 'L', t)].append(tuple(l))
            if len(l) == t:
                fams[(q, h, 'R', t)].append(tuple(r))
    return fams


def measure(code, T=200000, cap=4000):
    """The best anchor by `fibval == visit index`, then the form report."""
    best = None
    for key, ws in anchors(code, T).items():
        ws = ws[:cap]
        if len(ws) < 20:
            continue
        for off in (0, 1):
            vs = [None if not w or len(w) + off > 60
                  else sum(d * fibw(i + off) for i, d in enumerate(w))
                  for w in ws]
            n = cur = 0
            for i, v in enumerate(vs):
                cur = cur + 1 if (cur and vs[i - 1] is not None
                                  and v is not None and v == vs[i - 1] + 1) else 1
                n = max(n, cur)
            if best is None or n > best[0]:
                best = (n, len(ws), key, off, ws)
    if best is None:
        return None
    n, tot, key, off, ws = best
    rec = {'spec': code, 'anchor': '%s h=S%d %s |other|=%d' % (
        key[0], key[1], key[2], key[3]), 'off': off,
        'consecutive': n, 'visits': tot}
    # the value table, over the whole run rather than the cap
    seen = {}
    q0, h0, side, t0 = key
    for (q, l, h, r) in run(code, T):
        if q != q0 or h != h0:
            continue
        w, o = (r, l) if side == 'R' else (l, r)
        if len(o) != t0 or not w:
            continue
        v = sum(d * fibw(i + off) for i, d in enumerate(w))
        seen.setdefault(v, tuple(w))
    byk = defaultdict(list)
    for v, w in seen.items():
        byk[len(w)].append(v)
    rec['widths'] = []
    lim_ok = True
    for k in sorted(byk)[:12]:
        lo, hi = min(byk[k]), max(byk[k])
        # narrowest spelling: width k spans [fibw k .. fibsum k], and
        # `fibsum_S` (S (fibsum k) = fibw (S k)) is why the two ends meet.
        exp = (fibw(k + off), fibsum(k + off) - (fibsum(off) if off else 0))
        ok = (lo, hi) == exp and len(byk[k]) == hi - lo + 1
        lim_ok = lim_ok and (ok or k < 3)
        rec['widths'].append({'k': k, 'n': len(byk[k]), 'lo': lo, 'hi': hi,
                              'fam_lim_ok': ok})
    rec['fam_lim_ok'] = lim_ok
    rec['n_values'] = len(seen)
    rec['is_fibdec'] = sum(
        1 for v, w in seen.items() if tuple(fibdec(len(w), False, v)) == w)
    rec['is_no_adj_zero'] = sum(1 for w in seen.values() if no_adj_zero(w))
    rec['is_kernel_member'] = sum(1 for w in seen.values() if kernel_member(w))
    rec['d0_always_one'] = sum(1 for w in seen.values() if w[0] == 1)
    # the top of a width, and what the machine puts after it
    rec['tops'] = []
    for k in sorted(byk)[:8]:
        hi = max(byk[k])
        if hi + 1 in seen:
            rec['tops'].append({'k': k, 'v': hi, 'top': list(seen[hi]),
                                'succ': list(seen[hi + 1])})
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--steps', type=int, default=200000)
    a = ap.parse_args()
    for code in ([a.spec] if a.spec else ROWS):
        r = measure(code, a.steps)
        if r is None:
            print('%-30s -- no anchor' % code)
            continue
        n = r['n_values']
        print('%-30s %s off=%d  consec=%d/%d  values=%d' % (
            code, r['anchor'], r['off'], r['consecutive'], r['visits'], n))
        print('    fam_lim (widths span [fibw k .. fibsum k]): %s' %
              ('OK' if r['fam_lim_ok'] else 'NO'))
        print('    machine string == LadderFam.fibdec : %d/%d' % (r['is_fibdec'], n))
        print('    machine string in kernel automaton : %d/%d' % (r['is_kernel_member'], n))
        print('    machine string has no two 0s adjacent (LSB-first): %d/%d'
              % (r['is_no_adj_zero'], n))
        print('    digit 0 is a constant 1: %d/%d' % (r['d0_always_one'], n))
        for t in r['tops'][2:7]:
            print('    k=%d top v=%d %s -> %s' % (t['k'], t['v'], t['top'], t['succ']))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
