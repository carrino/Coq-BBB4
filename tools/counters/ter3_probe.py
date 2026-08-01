#!/usr/bin/env python3
"""UNTRUSTED (tools/): read `1RB1RC_1LA0LB_1LD0RD_1LB0RC` as a BASE-3 wall
counter, and measure its lap.

LADDER_PLAN 4w.  `tools/closeout/residue_map.tsv` calls this row `EXP3` with
alphabet `Ip` and blocker "no interior chain", and `docs/LADDER_NOFAM.md`
measures `1 1 1 3 3 9 9 27` distinct strings per width -- ratio 3, i.e. a
base-3 counter -- without locating the anchor.  This locates it, and the
reading is exact over 75,006 consecutive anchor visits with zero failures.

    anchor      (StA, ([], S1, S1 :: <digits>))
    digits      2 cells each, LSB nearest the head, {00, 10, 11} = {0, 1, 2}
    top digit   TRUNCATED -- a `1` alone is digit 1, `11` is digit 2, and a
                top digit 0 never occurs (that is the same "a cconf carries
                no trailing blank" fact `lpad_eqb` states)

That alphabet is `theories/Counters/Ter3WallB.v`'s, digit for digit, and the
truncated top is `TernCounter`'s `tsucc` (overflow writes a fresh digit)
against `tsuccT` (a terminator sits past the top digit).  The lap is AFFINE
in the carry length `c` (the number of trailing 2s), in exactly two branches:

    gap  =  6c + 4    or    6c + 6

measured for c = 0..7 with no third value in any class.  So this row wants
the base-3 module that already exists plus a `LapGlue.glue_neverqh` closer
(it is a four-state row -- `StA` is the target of `B0` -- so its theorem is
`NeverQuasiHaltsSt`, not the `iqh` the three-state `Ter3Wall*` rows carry).

    python3 tools/counters/ter3_probe.py [--steps N]
"""
import argparse
from collections import defaultdict

SPEC = "1RB1RC_1LA0LB_1LD0RD_1LB0RC"
DIG = {(0, 0): 0, (1, 0): 1, (1, 1): 2}


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def anchors(spec, T):
    """(step, word-right-of-the-head) at every (StA, left empty, head S1)."""
    tab = parse(spec)
    tape = defaultdict(int)
    pos, st, lo, hi = 0, 0, 0, 0
    for n in range(T):
        sym = tape[pos]
        if st == 0 and sym == 1 and all(tape[x] == 0 for x in range(lo, pos)):
            r = [tape[x] for x in range(pos + 1, hi + 1)]
            while r and r[-1] == 0:
                r.pop()
            yield (n, r)
        e = tab[(st, sym)]
        if e is None:
            return
        w, d, ns = e
        tape[pos] = w
        lo, hi = min(lo, pos), max(hi, pos)
        pos += d
        st = ns
        lo, hi = min(lo, pos), max(hi, pos)


def decode(w):
    """`w` is the word right of the head with the wall's neighbour `1`
    already stripped.  Returns the base-3 value, or None."""
    ds, i = [], 0
    while i + 1 < len(w):
        d = DIG.get((w[i], w[i + 1]))
        if d is None:
            return None
        ds.append(d)
        i += 2
    if i < len(w):
        if w[i] != 1:
            return None
        ds.append(1)
    if ds and ds[-1] == 0:
        return None
    return sum(d * 3 ** k for k, d in enumerate(ds))


def carry(v):
    c = 0
    while v % 3 == 2:
        c += 1
        v //= 3
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=600000)
    a = ap.parse_args()
    ws = list(anchors(SPEC, a.steps))
    vals, bad = [], 0
    for _, w in ws:
        if not w or w[0] != 1:
            bad += 1
            vals.append(None)
        else:
            vals.append(decode(w[1:]))
    fails = sum(1 for i in range(1, len(vals))
                if vals[i] is None or vals[i - 1] is None
                or vals[i] != vals[i - 1] + 1)
    print("%s" % SPEC)
    print("  anchor visits            %d" % len(ws))
    print("  prefix failures          %d" % bad)
    print("  consecutive-value fails  %d" % fails)
    print("  values                   %s ... %s" % (vals[:8], vals[-1]))
    gaps = defaultdict(set)
    for (n0, _), (n1, _), v in zip(ws, ws[1:], vals):
        if v is not None:
            gaps[carry(v)].add(n1 - n0)
    print("  lap gap by carry length:")
    for c in sorted(gaps)[:10]:
        print("    c=%-3d %s   (6c+4 = %d, 6c+6 = %d)"
              % (c, sorted(gaps[c]), 6 * c + 4, 6 * c + 6))


if __name__ == '__main__':
    main()
