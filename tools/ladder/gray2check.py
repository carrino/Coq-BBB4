#!/usr/bin/env python3
"""UNTRUSTED oracle for the (Gray, 2) case split, stated exactly as
`LadderCheck` states it.

LADDER_PLAN 4n's probe FITTED the classes from the family's own successor and
recovered 4i's four verbatim.  This does the other half: it takes the four
classes AS THE KERNEL WILL STATE THEM -- with the parity predicate `P`, the
four-way split that replaces `digs_decomp`, and the top shape -- and checks
them by enumeration over the orbit of every gray row.  It is the oracle 4n's
own instruction names ("use it as the oracle while you state the lemma"), and
it is here so the Coq statements are checked BEFORE they are proved.

What is checked, per row and per width:

  * the PARITY invariant: every member of the orbit has the same digit-sum
    parity, and the fill target does too (this is what makes `P` global and an
    invariant rather than a side condition);
  * the four-way SPLIT: every member is the top of its width or matches one of
    the four classes at some (n, rest) whose digits are in range;
  * the CLASS LAW: `fam_next` on every match is what the class says;
  * the TOP SHAPE: the top of a width is `[1] ++ 0^(k-2) ++ [1]` at even
    parity and `0^(k-1) ++ [1]` at odd parity -- the largest MEMBER, not the
    largest value.

Usage:  gray2check.py [SWEEP.jsonl] [--kmax K]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

DEFAULT_SWEEP = os.path.join(HERE, 'core61_sweep.jsonl')


# ------------------------------------------------------- the numeration ----
# `LadderFam.gdec`/`genc`/`val_pos`/`pos_of` at base 2, transcribed.

def gdec(b, ds):
    out = []
    for d in reversed(ds):
        out.append((d + (out[-1] if out else 0)) % b)
    return list(reversed(out))


def genc(b, ns):
    out = []
    for i, n in enumerate(ns):
        nxt = ns[i + 1] if i + 1 < len(ns) else 0
        out.append((n % b + (b - nxt % b)) % b)
    return out


def val_pos(b, ds):
    v = 0
    for d in reversed(ds):
        v = v * b + d
    return v


def pos_of(b, k, v):
    out = []
    for _ in range(k):
        out.append(v % b)
        v //= b
    return out


class Fam:
    """`LadderFam.Fam` on the certificate JSON, for a one-phase gray family."""

    def __init__(self, cert):
        f = cert['family']
        self.spec = cert['spec']
        self.b = f['base']
        self.step = f.get('value_step_per_anchor_visit', 1)
        fills = cert.get('fill_by_phase') or [cert['fill']]
        self.fill = fills[0]
        self.nph = len(fills)
        self.boot = list(cert['boot']['digits_lsb_first'])

    def value(self, ds):
        return val_pos(self.b, gdec(self.b, ds))

    def of_value(self, v, k):
        if v >= self.b ** k:
            return None
        return genc(self.b, pos_of(self.b, k, v))

    def is_top(self, ds):
        return self.b ** len(ds) - 1 < self.value(ds) + self.step

    def filled(self, k):
        f = self.fill
        pre, suf = list(f['target_prefix']), list(f['target_suffix'])
        n = k + f['widens_by'] - len(pre) - len(suf)
        if n < 0:
            return None
        return pre + [f['target_fill_digit']] * n + suf

    def next_ds(self, ds):
        if self.is_top(ds):
            return self.filled(len(ds))
        return self.of_value(self.value(ds) + self.step, len(ds))


# ------------------------------------------------------------ the classes --
# 4i's four, VERBATIM, as (u, t, w) -> (u', t', w').  The odd-parity family's
# classes are these with the two sides exchanged; nothing else moves, which is
# why one record and one `ClassSucc` still serve both.

GRAY2_EVEN = [
    (([0, 0], 0, []), ([1, 1], 0, [])),
    (([0, 1], 1, []), ([1, 0], 1, [])),
    (([1], 0, [1, 0]), ([0], 0, [1, 1])),
    (([1], 0, [1, 1]), ([0], 0, [1, 0])),
]


def classes(p):
    """4i's four at the family's own parity `p`.  The odd family's classes are
    the even family's with the two sides EXCHANGED -- one record, one
    `ClassSucc`, and `p` is a parameter of the class rather than a second
    table.  Written out, the four are

        [p;p]     0^n              -> [1-p;1-p] 0^n
        [p;1-p]   1^n              -> [1-p;p]   1^n
        [1-p]     0^n ++ [1;p]     -> [p]       0^n ++ [1;1-p]
        [1-p]     0^n ++ [1;1-p]   -> [p]       0^n ++ [1;p]

    which is `GRAY2_EVEN` at `p = 0`."""
    q = 1 - p
    return [((([p, p], 0, [])), (([q, q], 0, []))),
            ((([p, q], 1, [])), (([q, p], 1, []))),
            ((([q], 0, [1, p])), (([p], 0, [1, q]))),
            ((([q], 0, [1, q])), (([p], 0, [1, p])))]


def cls_side(c, n, rest):
    u, t, w = c
    return list(u) + [t] * n + list(w) + list(rest)


def split(p, ds):
    """The four-way case split the kernel states, as a decision procedure --
    the replacement for `digs_decomp`.

    Returns ('top',) or ('class', i, n, rest).  Every member of a width is one
    of the four classes or the top, and the discriminator is the FIRST digit:

      * `ds[0] = p` -- the class fires at run length 0, its fixed word is the
        first two digits and everything after is the opaque tail (classes 0
        and 1, picked by `ds[1]`);
      * `ds[0] = 1-p` -- walk the zeros after it.  There IS a 1 after them,
        because `(1-p) ++ 0^(k-1)` has digit sum `1-p` and the parity says
        `p`.  If that 1 is the LAST digit the string is the top; otherwise the
        digit past it picks class 2 or 3 and `n` is the number of zeros."""
    k = len(ds)
    q = 1 - p
    if k < 2:
        return None
    if ds[0] == p:
        return ('class', 0 if ds[1] == p else 1, 0, ds[2:])
    n = 0
    while 1 + n < k and ds[1 + n] == 0:
        n += 1
    if 1 + n >= k:
        return None            # (1-p) ++ 0^(k-1): the parity forbids it
    if 1 + n == k - 1:
        return ('top',)
    return ('class', 2 if ds[2 + n] == p else 3, n, ds[3 + n:])


def top_shape(p, k):
    """The largest MEMBER of width k: `[1-p] ++ 0^(k-2) ++ [1]`, value
    `2^k - 2 + p`.  At even parity `2^k - 1` is odd and not a member at all,
    so this is NOT the string `of_value` computes for the width's ceiling."""
    return [1 - p] + [0] * (k - 2) + [1]


# ---------------------------------------------------------------- checking --

def check(cert, kmax=13, verbose=False):
    F = Fam(cert)
    out = {'spec': F.spec, 'b': F.b, 'step': F.step, 'nph': F.nph}
    if F.b != 2 or F.step != 2 or F.nph != 1:
        out['stop'] = 'not a one-phase (gray, 2) family at base 2'
        return out
    par = sum(F.boot) % 2
    out['parity'] = par

    # the orbit, from the boot
    ds, seen, orb = list(F.boot), set(), []
    while len(ds) <= kmax:
        key = tuple(ds)
        if key in seen:
            break
        seen.add(key)
        orb.append(list(ds))
        nx = F.next_ds(ds)
        if nx is None:
            break
        ds = list(nx)
    out['orbit'] = len(orb)
    out['widths'] = sorted({len(d) for d in orb})

    bad = []

    # (1) the parity is an invariant of the orbit, and of the fill target
    for d in orb:
        if sum(d) % 2 != par:
            bad.append('orbit member %s has the wrong parity' % d)
            break
    for k in range(2, kmax + 2):
        t = F.filled(k)
        if t is None:
            bad.append('the fill has no target at width %d' % k)
        elif sum(t) % 2 != par:
            bad.append('the fill target at width %d is %s, parity %d'
                       % (k, t, sum(t) % 2))

    # (2)-(4) over EVERY string of every width with the right parity, not only
    # the orbit: the case split is a lemma about members, and a member is any
    # bounded string of that parity.
    cls = classes(par)
    nstr = ntop = 0
    for k in range(2, kmax + 1):
        for v in range(2 ** k):
            d = [(v >> i) & 1 for i in range(k)]
            if sum(d) % 2 != par:
                continue
            nstr += 1
            r = split(par, d)
            if r is None:
                bad.append('width %d: %s is in no case' % (k, d))
                continue
            if r[0] == 'top':
                ntop += 1
                if not F.is_top(d):
                    bad.append('width %d: %s is split as the top and is not'
                               % (k, d))
                if d != top_shape(par, k):
                    bad.append('width %d: top %s is not the shape %s'
                               % (k, d, top_shape(par, k)))
                continue
            _, i, n, rest = r
            lhs, rhs = cls[i]
            if cls_side(lhs, n, rest) != d:
                bad.append('width %d: class %d at n=%d does not rebuild %s'
                           % (k, i, n, d))
                continue
            if F.is_top(d):
                bad.append('width %d: %s is the top and is split as class %d'
                           % (k, d, i))
                continue
            want = cls_side(rhs, n, rest)
            got = F.next_ds(d)
            if got != want:
                bad.append('width %d: class %d on %s gives %s, wanted %s'
                           % (k, i, d, got, want))

    # (5) the top of a width is a member, is the top, and there is exactly one
    for k in range(2, kmax + 1):
        t = top_shape(par, k)
        if sum(t) % 2 != par:
            bad.append('the top shape at width %d has the wrong parity' % k)
        if not F.is_top(t):
            bad.append('the top shape at width %d is not the top' % k)
        if F.value(t) != 2 ** k - 2 + par:
            bad.append('the top shape at width %d has value %d'
                       % (k, F.value(t)))

    out['strings_checked'] = nstr
    out['tops'] = ntop
    out['bad'] = bad[:20]
    out['ok'] = not bad
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('sweep', nargs='?', default=DEFAULT_SWEEP)
    ap.add_argument('--kmax', type=int, default=13)
    a = ap.parse_args()

    rows = {}
    for l in open(a.sweep):
        if l.strip():
            o = json.loads(l)
            rows[o['spec']] = o

    nok = n = 0
    for spec in sorted(rows):
        o = rows[spec]
        if not o.get('closed'):
            continue
        if o['family'].get('code') != 'gray':
            continue
        r = check(o, kmax=a.kmax)
        n += 1
        if r.get('stop'):
            print('%-33s SKIP %s' % (spec, r['stop']))
            continue
        nok += bool(r['ok'])
        print('%-33s parity=%d  %s  %d strings, %d tops, widths %s'
              % (spec, r['parity'], 'OK' if r['ok'] else 'BAD',
                 r['strings_checked'], r['tops'], r['widths']))
        for b in r['bad']:
            print('    %s' % b)
    print('\n%d of %d gray rows check out' % (nok, n))
    return 0 if nok == n else 1


if __name__ == '__main__':
    sys.exit(main())
