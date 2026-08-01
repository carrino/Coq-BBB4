#!/usr/bin/env python3
"""UNTRUSTED (tools/): sweep EVERY blank-side anchor against EVERY 2-cell
radix, and report which (anchor, alphabet) pairs read a row as a counter.

`ter3_probe.py` measures ONE anchor under ONE alphabet, because 4w already
knew both for `1RB1RC_1LA0LB_1LD0RD_1LB0RC`.  Pointing it at a row whose
anchor is elsewhere prints "anchor visits 0", which is not a verdict about
the row -- it is a verdict about the hard-coded shape.  This sweeps instead,
so a negative is a MEASUREMENT.

`docs/CORE_3STATE.md` §2 is the reason this has to sweep alphabets and not
just anchors: `residue_map.tsv` labels the base-3 `Ter3Wall*` rows `EXP3`
because "read at base 2 their lap grows like 3^j", and they are NOT base 2.
So "I found an exact base-2 reading" does not by itself refute base 3 -- the
two can coexist at different anchors, and only a sweep that finds no base-3
reading anywhere settles it.

Searched, at each (state, head symbol) with one side all-blank:

    counter side   the non-blank side, digits nearest the head first
    prefix         0, 1 or 2 fixed cells between the head and the digits
                   (`1RB1RC_1LA0LB_1LD0RD_1LB0RC`'s wall neighbour is one
                   such cell, and skipping it is what `ter3_probe.decode`
                   hard-codes as `w[1:]`)
    digit words    every 2-subset (base 2) and 3-subset (base 3) of
                   {00, 01, 10, 11}, digit 0 forced to `00`
    top digit      TRUNCATED -- a lone `1` is the top digit, and a top
                   digit 0 never occurs (`lpad_eqb`)

and scored by the longest run of CONSECUTIVE decoded values, which is the
only signal that distinguishes a numeration from a coincidence.  For every
reading that runs the whole visit list it then reports the lap by carry
length, and whether that lap is AFFINE (`a*c + b`, what a ladder needs) or
GEOMETRIC (`A*r^c + B*c + C`, what `LapGlue`'s existential step count still
takes but no ladder arm does).

    python3 tools/counters/ter3_scan.py SPEC [SPEC ...] [--steps N]
"""
import argparse
import itertools
from collections import defaultdict

LAB = "ABCD"
CELLS = [(0, 0), (0, 1), (1, 0), (1, 1)]


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def visits(spec, T):
    """Every step, as (n, state, head symbol, left word, right word).

    Both words are given nearest-the-head first, with the far end's blanks
    stripped, so `()` means "that side is blank".
    """
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


def decode(w, dig, base):
    """`w` nearest-head-first, 2 cells per digit, top digit truncated."""
    ds, i = [], 0
    while i + 1 < len(w):
        d = dig.get((w[i], w[i + 1]))
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
    return sum(d * base ** k for k, d in enumerate(ds))


def longest_consecutive(vals):
    best = cur = 0
    for i, v in enumerate(vals):
        if v is not None and i and vals[i - 1] is not None and v == vals[i - 1] + 1:
            cur += 1
        else:
            cur = 1 if v is not None else 0
        best = max(best, cur)
    return best


def carry(v, base):
    c = 0
    while v % base == base - 1:
        c += 1
        v //= base
    return c


def fit(gaps):
    """Name the lap law over `{carry length: gap set}`, or return None.

    A class with more than one gap is a lap with that many BRANCHES (base 3
    at `1RB1RC_1LA0LB_1LD0RD_1LB0RC` has two, `6c + 4` and `6c + 6`), so fit
    each branch rather than calling the whole thing unresolved.
    """
    cs = sorted(gaps)
    if len(cs) < 4:
        return None
    k = len(gaps[cs[0]])
    if k > 1:
        # The largest carry lengths are seen only once or twice in a finite
        # run, so their classes are short a branch.  Fit on the classes that
        # are complete, and say how many those are.
        cs = [c for c in cs if len(gaps[c]) == k]
        if k > 3 or len(cs) < 4:
            return None
        parts = [fit1(cs, [sorted(gaps[c])[i] for c in cs]) for i in range(k)]
        if any(p is None for p in parts):
            return None
        return "%d branches: %s" % (k, "   |   ".join(parts))
    return fit1(cs, [next(iter(gaps[c])) for c in cs])


def fit1(cs, y):
    """Name one branch's law over the carry lengths `cs`."""
    if cs != list(range(cs[0], cs[0] + len(cs))):
        return None
    d = [y[i + 1] - y[i] for i in range(len(y) - 1)]
    if len(set(d)) == 1:
        return "AFFINE  %dc + %d" % (d[0], y[0] - d[0] * cs[0])
    dd = [d[i + 1] - d[i] for i in range(len(d) - 1)]
    if len(dd) >= 2 and all(x for x in dd) and len({
            (dd[i + 1] * 1.0 / dd[i]) for i in range(len(dd) - 1)}) == 1:
        r = dd[1] // dd[0]
        # y = A*r^c + B*c + C ; solve on the first three points.
        A2 = dd[0] * 2.0 / ((r - 1) ** 2 * r ** cs[0])
        B = (d[0] - A2 * (r - 1) * r ** cs[0] / 2.0)
        C = y[0] - A2 * r ** cs[0] / 2.0 - B * cs[0]
        return "GEOM r=%d  %s*%d^c + %gc + %g" % (
            r, ("%g" % (A2 / 2.0)), r, B, C)
    return "IRREGULAR"


def alphabets():
    for base in (2, 3):
        for rest in itertools.combinations([c for c in CELLS if c != (0, 0)],
                                           base - 1):
            yield base, dict([((0, 0), 0)] + [(c, i + 1)
                                              for i, c in enumerate(rest)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='+')
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--min-run', type=int, default=64)
    a = ap.parse_args()
    for spec in a.specs:
        print("=" * 72)
        print(spec)
        ev = list(visits(spec, a.steps))
        for side in ('R', 'L'):
            grp = defaultdict(list)
            for n, st, sym, L, R in ev:
                near, far = (R, L) if side == 'R' else (L, R)
                if not far:
                    grp[(st, sym)].append((n, near))
            for key in sorted(grp):
                ws = grp[key]
                if len(ws) < a.min_run:
                    continue
                for pre in (0, 1, 2):
                    if any(len(w) < pre for _, w in ws):
                        continue
                    # The skipped cells have to BE fixed, or they are not a
                    # prefix -- they are part of the counter.
                    if len({w[:pre] for _, w in ws}) != 1:
                        continue
                    for base, dig in alphabets():
                        vals = [decode(w[pre:], dig, base) for _, w in ws]
                        run = longest_consecutive(vals)
                        if run < a.min_run or run < len(ws) * 0.9:
                            continue
                        gaps = defaultdict(set)
                        for (n0, _), (n1, _), v in zip(ws, ws[1:], vals):
                            if v is not None:
                                gaps[carry(v, base)].add(n1 - n0)
                        names = {v: "%d%d" % c for c, v in dig.items()}
                        print("  %s%d  counter on %s  prefix %s  base %d  "
                              "digits {%s}"
                              % (LAB[key[0]], key[1], side,
                                 "".join(map(str, ws[0][1][:pre])) or "-",
                                 base, ", ".join(names[i]
                                                 for i in sorted(names))))
                        print("      visits %-7d consecutive %-7d values 0..%s"
                              % (len(ws), run, vals[-1]))
                        print("      lap %s" % (fit(gaps) or "unresolved"))


if __name__ == '__main__':
    main()
