#!/usr/bin/env python3
"""UNTRUSTED (tools/): pin the anchor of Drozd's sixth row
`1RB0RD_1LB1LC_1RC0RA_0LB1RD` down to an exact `cconf`, and measure the lap.

Same four requirements as `kc3lap.py` / `bin3lap.py` (`docs/LADDER_PLAN.md`
§4z):

    * the word must be a numeral CELL FOR CELL -- here the counter runs
      RIGHTWARD from a left wall, so the word is the RIGHT list;
    * the other side must be literally empty and the head symbol fixed, so
      the anchor is a literal `(q, ([], s, W k))`;
    * the values must be consecutive with no offset;
    * the lap must be single-valued per class.

The measured word needs no numeral inductive at all: it is `rep [S1] k`,
a bare unary run, so the "counter" is a `nat`.

    python3 tools/counters/drz6lap.py [--steps N]
"""
import argparse
from collections import defaultdict

SPEC = "1RB0RD_1LB1LC_1RC0RA_0LB1RD"
LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def run(spec, T):
    """Yield (n, st, sym, L, R) with L head-outward-left, R head-outward-right,
    both stripped of trailing blanks -- exactly `cconf` coordinates."""
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
    ap.add_argument('--anchor', default='C0')
    a = ap.parse_args()
    aq, asym = LAB.index(a.anchor[0]), int(a.anchor[1])
    print("=" * 72)
    print("%s   anchor (St%s, ([], S%d, rep [S1] k))" % (SPEC, LAB[aq], asym))
    ev = list(run(SPEC, a.steps))
    print("  steps simulated: %d" % len(ev))

    # every visit to (aq, asym) with EMPTY left and a right that is all ones
    hits = [(n, len(R)) for n, st, sym, L, R in ev
            if st == aq and sym == asym and not L and all(x == 1 for x in R)]
    # visits to (aq,asym) with empty left that are NOT a bare unary run
    bad = [(n, R) for n, st, sym, L, R in ev
           if st == aq and sym == asym and not L and not all(x == 1 for x in R)]
    print("  R(k) visits: %d   non-unary (q,[],s,*) visits: %d"
          % (len(hits), len(bad)))
    if bad:
        print("    first non-unary at n=%d R=%s" % (bad[0][0], bad[0][1][:20]))
    print("  first 12 visits (n, k): %s" % (hits[:12],))
    ks = sorted({k for _, k in hits})
    print("  k values seen: %s%s" % (ks[:14], " ..." if len(ks) > 14 else ""))
    print("  k mod 4 seen: %s" % sorted({k % 4 for _, k in hits}))
    print("  boot: first visit at n=%d with k=%d" % (hits[0][0], hits[0][1]))
    # each k visited exactly once?
    cnt = defaultdict(int)
    for _, k in hits:
        cnt[k] += 1
    print("  k values visited more than once: %s"
          % [k for k in sorted(cnt) if cnt[k] > 1][:10])

    # half-lap table
    print("  half-laps  R(k) -> R(k'):")
    rows = []
    for (n0, k0), (n1, k1) in zip(hits, hits[1:]):
        rows.append((k0, k1, n1 - n0))
    for r in rows[:16]:
        print("    R(%-6d) -> R(%-6d)   %d" % r)

    # closed forms from the prompt
    print("  closed-form check:")
    ok = True
    for k0, k1, g in rows:
        if k0 % 4 == 2:
            i = (k0 - 2) // 4
            exp, tgt = 2 ** (2 * i + 3) - 1, 4 * i + 3
        else:
            i = (k0 - 3) // 4
            exp, tgt = 48 * 4 ** i - 6 * i - 15, 4 * i + 6
        if (g, k1) != (exp, tgt):
            ok = False
            print("    MISMATCH k=%d: got (%d,%d) want (%d,%d)"
                  % (k0, g, k1, exp, tgt))
    print("    both closed forms hold on all %d measured half-laps: %s"
          % (len(rows), ok))

    # Hvis: states in every FULL lap R(4i+2) -> R(4i+6)
    anch = [(n, k) for n, k in hits if k % 4 == 2]
    last = [[-1] * (len(ev) + 1) for _ in range(4)]
    for kk, (_, st, _, _, _) in enumerate(ev):
        for s in range(4):
            last[s][kk + 1] = kk if s == st else last[s][kk]
    miss = defaultdict(int)
    for (n0, _), (n1, _) in zip(anch, anch[1:]):
        for s in range(4):
            if last[s][n1] < n0:
                miss[s] += 1
    print("  full laps %d ; laps missing a state: %s"
          % (len(anch) - 1,
             {LAB[s]: c for s, c in miss.items()}
             or "NONE (all 4 states in every lap)"))

    # bare-unary screening of the two half tapes (re-report, cheap)
    ru = sum(1 for _, _, _, _, R in ev if all(x == 1 for x in R))
    lu = sum(1 for _, _, _, L, _ in ev if all(x == 1 for x in L))
    print("  right half-tape bare unary: %.2f%%   left: %.2f%%"
          % (100.0 * ru / len(ev), 100.0 * lu / len(ev)))


if __name__ == '__main__':
    main()
