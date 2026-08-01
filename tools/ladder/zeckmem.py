#!/usr/bin/env python3
"""ZECKMEM: the numeration the six surviving fibonacci rows actually count in,
checked against the orbit read off the machines.

LADDER_PLAN.md 4s measured all six rows (`valfam.py --numeration`) and found
them reading at anchor chains of 232-376 under weights 1, 2, 3, 5, 8, 13, 21 --
NOT the 1, 1, 2, 3, 5, 8 that `LadderCheck` section 11 states.  This script is
the oracle for the instance that would board them, in the tradition of
`fibmem.py` (4p) and `gray2check.py` (4o): every fact a Coq lemma would state,
enumerated against the machines first.  Do not state a lemma this has not
checked.

Run:  python3 tools/ladder/zeckmem.py            # the spec, from the blocks
      python3 tools/ladder/zeckmem.py --rows F   # ...and against the machines

THE FOUR FACTS.

1. MEMBERSHIP.  LSB-first, the strings are concatenations of the blocks `01`
   and `1`.  Equivalently: no two adjacent `0`s, and the top digit is `1`.
   Equivalently again, and this is the form that names it: the BIT-COMPLEMENT
   of the Zeckendorf strings (no two adjacent `1`s) of the same width with the
   top digit `0`.  Counts 1, 2, 3, 5, 8, 13, 21, 34 at widths 1..8.

   This is a DIFFERENT phi numeration from `(Fib, 1)`, not a re-indexing of it:
   `fibokb` restricts runs of `1`s (every maximal run even but the lowest) and
   this restricts runs of `0`s.  No reversal or complement of one is the other
   -- `--compare` prints the table.

2. THE TOP OF A WIDTH IS `1^k`, exactly as at `(Fib, 1)`.  So the fill arm's
   left-hand side is a bare run and section 11's shape carries over.

3. THE SPLIT IS TWO-WAY, on the low end, and BOTH classes fit the existing
   `Class` record -- `(u, t, w, u', t', w')`, lhs `u ++ t^n ++ w` -> rhs
   `u' ++ t'^n ++ w'` -- so `Class` does not widen for a fourth time:

       increment   0 ++ rest          ->  1 ++ rest
       carry       1^(2m+1) ++ [0]    ->  (01)^(m+1)

   i.e. u=[1], t=[1;1], w=[0]  ->  u'=[0;1], t'=[0;1], w'=[], at run length m.
   Both fire at offset 0 or 1 (`cs_u` empty or `[1]`), which is the same
   threshold 0..1 that 4p measured for the `(Fib, 1)` rows.

4. THE FILL IS PARITY-DEPENDENT, and this is the one genuinely new shape:

       1^k  ->  the ALTERNATING string of width k+1, whose low digit
                is (k+1) mod 2 -- `0` when k is odd, `1` when k is even

   `(Fib, 1)`'s fill target was a bare run of `0`, which `Fill`'s
   prefix/digit^n/suffix spells directly.  `(01)^m` is a run of a two-cell
   BLOCK, which it does not.  Two ways out, and 4s did not measure which is
   cheaper: re-read the rows at digit width 2, where the alternating target
   becomes a bare run of one digit; or give `Fill` a repeated block.  The
   parity itself is not new -- 4o made it a parameter for `(Gray, 2)`.

Nothing here carries proof weight."""
import argparse
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

BLOCKS = (frozenset({(0, 1), (1,)}), {0: frozenset({()})})
W = (1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610)


def members(k):
    """The width-k members, LSB-first, from the blocks `01` and `1`."""
    import valfam
    return sorted(valfam.gen_class(BLOCKS, k))


def member(ds):
    """The predicate a Coq [ClassSucc]'s [P] would be: no two adjacent 0s
    LSB-first, and the top digit set."""
    return bool(ds) and ds[-1] == 1 and not any(
        ds[i] == 0 and ds[i + 1] == 0 for i in range(len(ds) - 1))


def value(ds):
    return sum(d * W[i] for i, d in enumerate(ds))


def zeck(k):
    return {d for d in itertools.product((0, 1), repeat=k)
            if not any(d[i] and d[i + 1] for i in range(k - 1))}


def spell(ds):
    return ''.join(map(str, ds))


def check_membership(kmax=12):
    ok = True
    counts = []
    for k in range(1, kmax + 1):
        ms = set(members(k))
        counts.append(len(ms))
        pred = {d for d in itertools.product((0, 1), repeat=k) if member(d)}
        comp = {tuple(1 - x for x in d) for d in ms}
        zk = {d for d in zeck(k) if d[-1] == 0}
        if ms != pred:
            print('  FAIL k=%d: the predicate and the blocks disagree' % k)
            ok = False
        if comp != zk:
            print('  FAIL k=%d: not the complement of Zeckendorf' % k)
            ok = False
    fib = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233]
    if counts != fib[:kmax]:
        print('  FAIL counts %s' % counts)
        ok = False
    print('  membership: blocks == predicate == complement-Zeckendorf, '
          'counts %s' % counts[:8])
    return ok


def check_top(kmax=10):
    ok = True
    for k in range(1, kmax + 1):
        top = max(members(k), key=value)
        if top != (1,) * k:
            print('  FAIL k=%d: top is %s, not 1^k' % (k, spell(top)))
            ok = False
    print('  top of a width: 1^k at every width 1..%d' % kmax)
    return ok


def byvalue(kmax):
    out = {}
    for k in range(1, kmax + 1):
        for ds in members(k):
            out.setdefault(value(ds), []).append(ds)
    return out


def check_split(kmax=12):
    """Every interior member's successor is one of the two classes, and the
    class fires at offset 0 or 1.  Overlap 0, uncovered 0, wrong 0."""
    bv = byvalue(kmax)
    inc = carry = widen = bad = 0
    for k in range(1, kmax - 1):
        for ds in members(k):
            nxt = [x for x in bv.get(value(ds) + 1, []) if len(x) == k]
            if not nxt:
                widen += 1
                continue
            a, b = list(ds), list(nxt[0])
            if a[0] == 0 and b[0] == 1 and a[1:] == b[1:]:
                inc += 1
                continue
            # carry: 1^(2m+1) 0 -> (01)^(m+1), at offset 0 or 1
            hit = False
            for off in (0, 1):
                if a[:off] != b[:off]:
                    continue
                r = 0
                while off + r < k and a[off + r] == 1:
                    r += 1
                if r % 2 == 0 or off + r >= k or a[off + r] != 0:
                    continue
                m = (r - 1) // 2
                lhs = [1] * r + [0]
                rhs = list((0, 1)) * (m + 1)
                if (a[off:off + r + 1] == lhs and b[off:off + r + 1] == rhs
                        and a[off + r + 1:] == b[off + r + 1:]):
                    carry += 1
                    hit = True
                    break
            if not hit:
                bad += 1
                print('  FAIL %s -> %s (neither class)' % (spell(a), spell(b)))
    print('  split: %d increment + %d carry, %d widen (one per width), '
          '%d unexplained' % (inc, carry, widen, bad))
    return bad == 0


def check_fill(kmax=10):
    bv = byvalue(kmax + 2)
    ok = True
    shown = []
    for k in range(1, kmax + 1):
        top = (1,) * k
        nxt = [x for x in bv.get(value(top) + 1, []) if len(x) == k + 1]
        if not nxt:
            print('  FAIL k=%d: the top has no successor at width k+1' % k)
            ok = False
            continue
        got = nxt[0]
        want = tuple((i + k + 1) % 2 for i in range(k + 1))
        if got != want:
            print('  FAIL k=%d: fill is %s, the parity law says %s'
                  % (k, spell(got), spell(want)))
            ok = False
        shown.append('1^%d->%s' % (k, spell(got)))
    print('  fill: %s' % '  '.join(shown[:5]))
    print('        parity law: alternating of width k+1, low digit (k+1 mod 2)')
    return ok


def compare_fib1():
    """The table that says this is not [fibokb] under any transform."""
    from emit_ladder import fib_member
    print('  k  |ours| |fibokb|  identity reversed complement rev+comp')
    for k in range(1, 9):
        o = set(members(k))
        K = {d for d in itertools.product((0, 1), repeat=k)
             if fib_member(list(d))}
        rev = {tuple(reversed(d)) for d in o}
        comp = {tuple(1 - x for x in d) for d in o}
        rc = {tuple(1 - x for x in reversed(d)) for d in o}
        print('  %-2d %5d %8d  %8s %8s %10s %8s'
              % (k, len(o), len(K),
                 'MATCH' if o == K else '-', 'MATCH' if rev == K else '-',
                 'MATCH' if comp == K else '-', 'MATCH' if rc == K else '-'))


def check_rows(path):
    """The blocks and weights, read off each machine rather than assumed."""
    from engine import parse_tm
    from trace import simulate
    from discover import mine_shapes, build_ladder
    import valfam
    ok = True
    for spec in [l.strip() for l in open(path) if l.strip()]:
        tm = parse_tm(spec)
        snaps = simulate(tm, 20000)
        rules = build_ladder(tm, mine_shapes(snaps), time_cap=60.0)
        fams = valfam.find_families(tm, snaps, rules, numeration=True)
        w = [f for f in fams if f[0].weights is not None]
        if not w:
            print('  %-30s NO WEIGHTED FAMILY' % spec)
            ok = False
            continue
        f, _, ch = w[0]
        blocks = sorted(spell(b) for b in f.classes[0]) if f.classes else None
        good = (list(f.weights[:5]) == [1, 2, 3, 5, 8]
                and blocks == ['01', '1'])
        print('  %-30s q=%s h=%s l=%d chain=%3d blocks=%s  %s'
              % (spec, 'ABCD'[f.q], f.h, f.l, ch, blocks,
                 'OK' if good else 'DIFFERENT'))
        ok = ok and good
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', help='row list to read the blocks off the '
                                   'machines (slow: ~1 min a row)')
    ap.add_argument('--compare', action='store_true',
                    help='the (Fib, 1) comparison table')
    a = ap.parse_args()
    ok = True
    print('MEMBERSHIP'); ok &= check_membership()
    print('TOP');        ok &= check_top()
    print('SPLIT');      ok &= check_split()
    print('FILL');       ok &= check_fill()
    if a.compare:
        print('VS (Fib, 1)')
        compare_fib1()
    if a.rows:
        print('THE MACHINES')
        ok &= check_rows(a.rows)
    print('ZECKMEM: %s' % ('OK' if ok else 'FAILED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
