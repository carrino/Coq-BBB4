#!/usr/bin/env python3
"""UNTRUSTED: read a row's macro system off the raw simulator directly in
CCONF coordinates.

`extract.py` prints the transformation as a FRAME (a cell string plus a head
index).  Section 8 of docs/WAVE36_MXDYS_FOUR.md records that the frame form
hides the two things a Coq proof needs -- which rules read past the unary run,
and what happens at the tape edge -- and that the rules have to be re-derived
in the `cconf` triple before any Coq is written.  This does that
re-derivation mechanically instead of by hand:

    (l, s, R)   l = left half-tape NEAREST CELL FIRST, s = head symbol,
                R = length of the unary run to the right of the head.

The configuration it corresponds to is

    (StA, (l, s, rep [S1] R ++ S0 :: Z))

-- explicit blank, then a generic tail -- and the reader CHECKS that the
right half really is `1^R` then blanks, reporting IMPURE when it is not.  A
row that never reports IMPURE over its orbit is a finite word-rewriting
system and can be boarded the way M1/M4 were.

Usage:
    python3 tools/mxdys4/cconf_rules.py SPEC [--grid]      # rule grid
    python3 tools/mxdys4/cconf_rules.py SPEC --scan N      # orbit purity scan

Nothing here carries proof weight.
"""
import sys
from collections import defaultdict


def parse(code):
    tm = {}
    for si, part in enumerate(code.split('_')):
        st = 'ABCD'[si]
        for sym in (0, 1):
            f = part[3 * sym:3 * sym + 3]
            tm[(st, sym)] = (None if f in ('---', '1RZ')
                             else (int(f[0]), f[1], f[2]))
    return tm


def macro(code, l, s, R, gate='A', cap=200000):
    """One macro step: from (l, s, R) in state `gate`, run the RAW machine to
    the next `gate` configuration.  Returns (l', s', R', steps), None when it
    never comes back (the macro system is partial there), or ('IMPURE',) when
    the right half stops being a bare unary run."""
    tm = parse(code)
    tape = defaultdict(int)
    for i, b in enumerate(l):
        tape[-1 - i] = b
    tape[0] = s
    for i in range(R):
        tape[1 + i] = 1
    pos, st, t = 0, gate, 0
    lo, hi = -len(l), R
    while True:
        tr = tm[(st, tape[pos])]
        if tr is None:
            return None                              # halts
        w, d, n = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = n
        t += 1
        lo, hi = min(lo, pos), max(hi, pos)
        if st == gate:
            break
        if t > cap:
            return None                              # never returns
    Rp, j = 0, pos + 1
    while tape[j] == 1:
        Rp += 1
        j += 1
    while j <= hi:
        if tape[j] != 0:
            return ('IMPURE',)
        j += 1
    lp = [tape[k] for k in range(pos - 1, lo - 1, -1)]
    while lp and lp[-1] == 0:
        lp.pop()
    return (lp, tape[pos], Rp, t)


def sstr(l):
    return ''.join(map(str, l)) or '.'


LS = [[], [1], [0], [1, 1], [0, 1], [1, 0], [0, 0],
      [1, 1, 1], [0, 1, 1], [1, 0, 1], [0, 0, 1], [1, 1, 0]]


def grid(code, maxR=8):
    print('### %s   cconf macro steps  (l, s, R) -> (l\', s\', R\')' % code)
    print('###   l is NEAREST CELL FIRST;  right half is 1^R then S0 then Z')
    for s in (0, 1):
        for R in range(0, maxR + 1):
            print(' -- s=%d R=%d --' % (s, R))
            for l in LS:
                r = macro(code, l, s, R)
                if r is None:
                    print('    l=%-5s -> (never returns to StA)' % sstr(l))
                elif r[0] == 'IMPURE':
                    print('    l=%-5s -> IMPURE RIGHT HALF' % sstr(l))
                else:
                    lp, sp, Rp, t = r
                    print('    l=%-5s -> l\'=%-10s s\'=%d R\'=%d  t=%d'
                          % (sstr(l), sstr(lp), sp, Rp, t))


def scan(code, n):
    """Walk the REAL orbit in macro steps and confirm the right half stays a
    bare unary run.  This is the lever test."""
    tm = parse(code)
    tape = defaultdict(int)
    pos, st, t = 0, 'A', 0
    lo = hi = 0
    steps = impure = 0
    maxl = maxR = 0
    while steps < n:
        # read off at StA
        if st == 'A':
            R, j = 0, pos + 1
            while tape[j] == 1:
                R += 1
                j += 1
            ok = all(tape[k] == 0 for k in range(j, hi + 1))
            if not ok:
                impure += 1
            ll = [tape[k] for k in range(pos - 1, lo - 1, -1)]
            while ll and ll[-1] == 0:
                ll.pop()
            maxl, maxR = max(maxl, len(ll)), max(maxR, R)
            steps += 1
        tr = tm[(st, tape[pos])]
        if tr is None:
            print('HALTS at raw step %d' % t)
            return
        w, d, nx = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = nx
        t += 1
        lo, hi = min(lo, pos), max(hi, pos)
    print('%s: %d StA configurations over %d raw steps' % (code, steps, t))
    print('  impure right halves: %d   %s' % (
        impure, 'LEVER APPLIES' if impure == 0 else 'lever does NOT apply'))
    print('  max |l| = %d   max R = %d' % (maxl, maxR))


def main():
    code = sys.argv[1]
    if '--scan' in sys.argv:
        i = sys.argv.index('--scan')
        n = int(sys.argv[i + 1]) if len(sys.argv) > i + 1 else 200000
        scan(code, n)
    else:
        grid(code)


if __name__ == '__main__':
    main()
