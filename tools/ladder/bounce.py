#!/usr/bin/env python3
"""UNTRUSTED: look for a BOUNCER COUNTER -- a counter read at a sweep's
turning point, separated from the head by a spacer that grows with the lap.

Generalised from John's two reads (LADDER_PLAN 4j).  The searcher
(`valfam.py`) anchors on a (state, head symbol) pair and matches a FIXED
near-head prefix (`Fam.read`: `base[:len(pre)] != pre -> None`), so a spacer
of `0^(2k+5)` never matches at any anchor and the row is filed under "no
counter reading at any anchor".  This probe drops that assumption and
nothing else:

  * lap events are the times the head reaches a NEW extreme, either side;
  * at each lap, either side of the head is a candidate counter side;
  * a leading run of one symbol is allowed to be a SPACER, and its length is
    allowed to grow with the lap;
  * what remains is decoded binary or gray, LSB-first or MSB-first;
  * only every s-th lap need be a member (s = 1..4, any offset).

A hit is: spacer length affine in the lap index AND value affine in it with
a positive step -- the same two facts `valfam` looks for, minus the fixed
prefix.

VALIDATE BEFORE BELIEVING A MISS: `--selftest` re-finds John's two rows.  A
miss here is a statement about this probe, not about the machine -- which is
the error LADDER_PLAN 4g names and 4j repeats.

Usage:  bounce.py SPEC...   |   bounce.py --list FILE   |   bounce.py --selftest
"""
import argparse
import sys

from tapes import parse_tm, rle

KNOWN = ['0RB0RD_1LC1RB_1RA0LC_1LB0LC', '0RB0RD_1LC1RB_1RA0LC_1LD0LC']


def laps(spec, steps, want):
    """Two SEPARATE lap streams: new-leftmost events, and new-rightmost.

    Keeping them apart matters -- interleaving the two scrambles the stride,
    which is what made the first version of this probe miss both of John's
    rows.  Left is head-nearest-first, so both sides read outward."""
    tab = parse_tm(spec)
    tape, pos, q = {}, 0, 0
    lo = hi = 0
    west, east = [], []
    for _ in range(steps):
        h = tape.get(pos, 0)
        tr = tab.get((q, h))
        if tr is None:
            return (west, east), True
        w, d, q2 = tr
        tape[pos] = w
        np_ = pos + d
        grew_w, grew_e = np_ < lo, np_ > hi
        if grew_w or grew_e:
            lo, hi = min(lo, np_), max(hi, np_)
            snap = ([tape.get(i, 0) for i in range(np_ - 1, lo - 1, -1)],
                    [tape.get(i, 0) for i in range(np_ + 1, hi + 1)])
            (west if grew_w else east).append(snap)
            if len(west) >= want and len(east) >= want:
                return (west, east), False
        lo, hi = min(lo, np_), max(hi, np_)
        pos = np_
        q = q2
    return (west, east), False


def gray_decode_b(ds, b):
    r, acc = [], 0
    for d in reversed(ds):
        acc = (acc + d) % b
        r.insert(0, acc)
    return r


import itertools


def gray_decode_b(ds, b):
    r, acc = [], 0
    for d in reversed(ds):
        acc = (acc + d) % b
        r.insert(0, acc)
    return r


def strip_words(cells, sp, L):
    """Strip a leading run of [sp], then chunk into L-cell digit words."""
    i = 0
    while i < len(cells) and cells[i] == sp:
        i += 1
    rest = cells[i:]
    n = len(rest) // L
    return i, [tuple(rest[j * L:(j + 1) * L]) for j in range(n)]


def affine(xs):
    if len(xs) < 5:
        return None
    d = {xs[i + 1] - xs[i] for i in range(len(xs) - 1)}
    return list(d)[0] if len(d) == 1 else None


def probe(spec, steps=400000, want=60, min_samples=6):
    """Every (frontier, side, spacer symbol, digit width, stride, offset,
    alphabet ordering, code, bit order), tested for: spacer length affine in
    the lap index AND value affine in it with a positive step.

    The alphabet is built ACROSS the laps of a subsequence, not per lap --
    a value of 1^2 has only one distinct word, and requiring two per lap is
    what made the second version of this probe miss both of John's rows."""
    streams, halted = laps(spec, steps, want)
    if halted:
        return [('HALTS', None)]
    hits = []
    for wi, ev in enumerate(streams):
        for side in (0, 1):
            for sp in (0, 1):
                for L in (1, 2, 3):
                    per = [strip_words(e[side], sp, L) for e in ev]
                    for st in range(1, 5):
                        for o in range(st):
                            sub = per[o::st][:12]
                            if len(sub) < min_samples:
                                continue
                            zs = [z for z, _ in sub]
                            dz = affine(zs)
                            if dz is None:
                                continue
                            alpha = sorted({w for _, ws in sub for w in ws})
                            if not (2 <= len(alpha) <= 3):
                                continue
                            b = len(alpha)
                            for perm in itertools.permutations(alpha):
                                idx = {w: k for k, w in enumerate(perm)}
                                for bo in ('lsb', 'msb'):
                                    for code in ('binary', 'gray'):
                                        vs = []
                                        for _, ws in sub:
                                            ds = [idx[w] for w in ws]
                                            if bo == 'msb':
                                                ds = list(reversed(ds))
                                            if code == 'gray':
                                                ds = gray_decode_b(ds, b)
                                            v = 0
                                            for d in reversed(ds):
                                                v = d + b * v
                                            vs.append(v)
                                        dv = affine(vs)
                                        if dv is None or dv <= 0:
                                            continue
                                        hits.append((
                                            '%s frontier, %s side, every %d '
                                            '(offset %d), digit width %d, '
                                            '%s/%s, digits %s'
                                            % ('WEST' if wi == 0 else 'EAST',
                                               'LEFT' if side == 0 else 'RIGHT',
                                               st, o, L, bo, code,
                                               '|'.join(''.join(map(str, w))
                                                        for w in perm)),
                                            'spacer %d^(%dk+%d), value %dk+%d'
                                            % (sp, dz, zs[0], dv, vs[0])))
    return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--steps', type=int, default=400000)
    a = ap.parse_args()
    if a.selftest:
        ok = True
        for s in KNOWN:
            h = probe(s, a.steps)
            print('%-30s %s' % (s, h[0] if h else 'MISS'))
            ok = ok and bool(h)
        print('selftest:', 'PASS' if ok else 'FAIL -- do not trust a miss')
        return 0 if ok else 1
    specs = a.specs or [l.split()[0] for l in open(a.list)
                        if l.strip() and not l.startswith('#')]
    for s in specs:
        h = probe(s, a.steps)
        if not h:
            print('%-30s --' % s)
        else:
            print('%-30s %s' % (s, h[0][0]))
            for w, d in h[:3]:
                print('%30s   %s | %s' % ('', w, d))
    return 0


if __name__ == '__main__':
    sys.exit(main())
