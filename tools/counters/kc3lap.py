#!/usr/bin/env python3
"""UNTRUSTED (tools/): pin the anchor of the KCOPY3 row
`1RB1RC_1LA1RA_0RC1LD_1LB0LD` down to an exact `cconf`, and state the lap law
per `cview` class at that anchor.

Same four requirements as `bin3lap.py` (`docs/LADDER_PLAN.md` §4z):

    * the LEFT word must be a numeral CELL FOR CELL (the counter grows
      leftward against a right wall here, so the word is the left list);
    * the other side must be literally empty and the head symbol fixed, so
      the anchor is a literal `(q, (W p, s, []))`;
    * the values must be 1, 2, 3, ... with no offset;
    * the lap must be single-valued per `cview` CLASS.

The measured word is NOT `Counters/Alph_000_111_111.Ap` -- see `--alph`.
It is `Ap` with the bit just below the MSB compressed from three cells to
ONE, i.e. a PACKED FRONTIER of two digits in four cells:

    Wk p = Fk p ++ [S1;S1;S1]
    Fk (xO xH) = [S0]                  Fk (xO q) = [S0;S0;S0] ++ Fk q
    Fk (xI xH) = [S1]                  Fk (xI q) = [S1;S1;S1] ++ Fk q

    python3 tools/counters/kc3lap.py [--steps N]
"""
import argparse
from collections import defaultdict

SPEC = "1RB1RC_1LA1RA_0RC1LD_1LB0LD"
LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def Ap(p):
    """`Counters/Alph_000_111_111.Ap_Alph_000_111_111`, head-outward."""
    out = []
    while p > 1:
        out += [1, 1, 1] if (p & 1) else [0, 0, 0]
        p >>= 1
    return tuple(out + [1, 1, 1])


def Fk(p):
    """The FIELD: three cells a digit, except the top digit, which is one."""
    out = []
    while p > 3:
        out += [1, 1, 1] if (p & 1) else [0, 0, 0]
        p >>= 1
    return tuple(out + ([p & 1] if p > 1 else []))


def Wk(p):
    """The anchor word: field then the three-cell marker."""
    return Fk(p) + ((1, 1, 1) if p > 1 else (1,))


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
    ap.add_argument('--steps', type=int, default=300000)
    ap.add_argument('--anchor', default='C1')
    a = ap.parse_args()
    aq, asym = LAB.index(a.anchor[0]), int(a.anchor[1])
    print("=" * 72)
    print("%s   anchor (St%s, (Wk p, S%d, []))" % (SPEC, LAB[aq], asym))
    ev = list(run(SPEC, a.steps))
    hits = [(n, L) for n, st, sym, L, R in ev
            if st == aq and sym == asym and not R]
    for name, F in (("Wk", Wk), ("Ap", Ap)):
        bad = [(n, p) for (n, w), p in zip(hits, range(1, len(hits) + 1))
               if w != F(p)]
        print("  anchor visits %d   %s mismatches %d   values %s..%s"
              % (len(hits), name, len(bad), 1, len(hits)))
        if bad:
            print("    first mismatch n=%d at p=%d" % (bad[0][0], bad[0][1]))
    # lap per cview class
    gaps = defaultdict(set)
    for (n0, _), (n1, _), p in zip(hits, hits[1:], range(1, len(hits))):
        j, r = cview(p)
        gaps[(j, r is None)].add(n1 - n0)
    byj = defaultdict(lambda: defaultdict(set))
    for (j, ov), g in gaps.items():
        byj[j]['ov' if ov else 'int'] |= g
    print("  lap by cview class (j = trailing set bits):")
    for j in sorted(byj)[:10]:
        print("    j=%-2d  interior %-24s overflow %s"
              % (j, sorted(byj[j]['int']) or '-', sorted(byj[j]['ov']) or '-'))
    multi = [(k, sorted(v)) for k, v in sorted(gaps.items()) if len(v) > 1]
    print("  classes with more than one lap length: %d %s" % (len(multi), multi[:3]))
    # states in every lap (glue_neverqh's Hvis)
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
             {LAB[s]: c for s, c in miss.items()}
             or "none (all 4 states in every lap)"))


if __name__ == '__main__':
    main()
