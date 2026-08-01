#!/usr/bin/env python3
"""UNTRUSTED (tools/): pin the `D0` anchor of the two base-2 EXP3 rows down
to an exact `cconf`, and state the lap law per carry class AT THAT ANCHOR.

`ter3_scan.py` (§4y) found the anchor and the alphabet by sweeping; what a
board needs is stronger than "some 2-cell radix decodes here":

    * the right word must be `MonoCounter.Wp p` CELL FOR CELL, so the
      numeral side is `Wp`/`cview` rather than a new inductive;
    * the left word must be empty and the head symbol fixed, so the anchor
      is a literal `(q, ([], s, Wp p))`;
    * the values must be 1, 2, 3, ... consecutively, so `Cf : positive ->
      cconf` fits with no offset;
    * the lap must be single-valued per `cview` CLASS -- and the class is
      what `cview` sees, `(j, Some q)` vs `(j, None)`, not just the carry
      length -- so a trichotomy over `cview` closes it.

Also reports which states occur in every lap (`glue_neverqh`'s `Hvis`), and
the per-unit step costs, so the unit rules can be stated before proving.

    python3 tools/counters/bin3lap.py [--steps N]
"""
import argparse
from collections import defaultdict

ROWS = ["1RB1LC_1LB1RA_0LC0LD_0RA0RD", "1RB1LC_1LC1RA_0LC0LD_0RA0RD"]
LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def Wp(p):
    """`MonoCounter.Wp`, as a tuple of 0/1 cells."""
    out = []
    while p > 1:
        out += [0, p & 1]
        p >>= 1
    return tuple(out + [0, 1])


def cview(p):
    """`MonoCounter.cview`: (trailing set bits, None iff p = 2^j - 1)."""
    j = 0
    while p > 1 and p & 1:
        j += 1
        p >>= 1
    return (j + 1, None) if p == 1 else (j, p >> 1)


def run(spec, T):
    tab = parse(spec)
    tape = defaultdict(int)
    pos, st, lo, hi = 0, 0, 0, 0
    for n in range(T):
        sym = tape[pos]
        L = [tape[x] for x in range(lo, pos)][::-1]
        R = [tape[x] for x in range(pos + 1, hi + 1)]
        while L and L[-1] == 0:
            L.pop()
        while R and R[-1] == 0:
            R.pop()
        yield (n, st, sym, tuple(L), tuple(R))
        e = tab[(st, sym)]
        if e is None:
            return
        w, d, ns = e
        tape[pos] = w
        lo, hi = min(lo, pos), max(hi, pos)
        pos += d
        st = ns
        lo, hi = min(lo, pos), max(hi, pos)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--anchor', default='D0')
    a = ap.parse_args()
    aq, asym = LAB.index(a.anchor[0]), int(a.anchor[1])
    for spec in ROWS:
        print("=" * 72)
        print("%s   anchor (St%s, ([], S%d, Wp p))" % (spec, LAB[aq], asym))
        ev = list(run(spec, a.steps))
        hits = [(n, R) for n, st, sym, L, R in ev
                if st == aq and sym == asym and not L]
        # 1. is every anchor word exactly Wp of a consecutive p?
        bad = [(n, w) for (n, w), p
               in zip(hits, range(1, len(hits) + 1)) if w != Wp(p)]
        print("  anchor visits %d   Wp mismatches %d   values %s..%s"
              % (len(hits), len(bad), 1, len(hits)))
        if bad:
            print("    first mismatch n=%d  %s" % (bad[0][0], bad[0][1]))
        # 2. lap per cview class
        gaps = defaultdict(set)
        for (n0, _), (n1, _), p in zip(hits, hits[1:], range(1, len(hits))):
            j, r = cview(p)
            gaps[(j, r is None)].add(n1 - n0)
        byj = defaultdict(lambda: defaultdict(set))
        for (j, ov), g in gaps.items():
            byj[j]['ov' if ov else 'int'] |= g
        print("  lap by cview class (j = trailing set bits):")
        for j in sorted(byj)[:9]:
            print("    j=%-2d  interior %-22s overflow %s"
                  % (j, sorted(byj[j]['int']) or '-',
                     sorted(byj[j]['ov']) or '-'))
        multi = [(k, sorted(v)) for k, v in sorted(gaps.items()) if len(v) > 1]
        print("  classes with more than one lap length: %d %s"
              % (len(multi), multi[:3]))
        # 3. states in every lap (glue_neverqh's Hvis)
        # last[s][n] = last index <= n at which state s ran (-1 if never),
        # so "state s occurs in [n0, n1)" is one comparison per lap.
        last = [[-1] * (len(ev) + 1) for _ in range(4)]
        for k, (_, st, _, _, _) in enumerate(ev):
            for s in range(4):
                last[s][k + 1] = k if s == st else last[s][k]
        miss = defaultdict(int)
        for (n0, _), (n1, _) in zip(hits, hits[1:]):
            for s in range(4):
                if last[s][n1] < n0:
                    miss[s] += 1
        print("  laps %d ; laps missing a state: %s"
              % (len(hits) - 1,
                 {LAB[s]: c for s, c in miss.items()} or "none (all 4 states"
                 " in every lap)"))


if __name__ == '__main__':
    main()
