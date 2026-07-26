#!/usr/bin/env python3
"""Recon probe for the blockdbl_counter family (#11, #13, #28).

BBB's verify.c (verify_blockdbl_counter) models these as SOLID-BLOCK
doubling counters:

  side R:  D(j) = 1^m 0 1^t,   head on the RIGHTMOST 1, state edge
  side L:  D(j) = 1 0^z 1^m,   head on the LEFTMOST  1, state edge

with m(j) = ma*2^(j-1) + mb,  m -> 2m + mdbl
     t(j) = ta*j + tb,        t -> t + ta      (side L: t is the 0^z spacer)

One macro lap collapses the solid block leftward (|delta|=1 run cross)
and spreads it back doubled rightward (|delta|=1).  This script replays
the raw stepper from D(j), prints the turnaround structure, and reports
the exact phase decomposition so the Coq units can be read off.

Usage:  probe_bd.py 13 [jmin] [jmax] [--trace]
"""
import sys

LAB = "ABCD"

# machine -> (spec, edge, side, ma, mb, mdbl, ta, tb)   side 0=R, 1=L
MACHINES = {
    '11': ("1RB0LD_1RC0RC_1LA1RB_0LC0LD", 2, 0, 3, 1, -1, 2, -1),
    '13': ("1RB0RB_1LC1RA_1RA0LD_0LB0LD", 1, 0, 3, 0,  0, 2, -1),
    '28': ("1RB1LC_1LC1RD_1LA0LC_0RD0RB", 2, 1, 4, -1, 1, 2,  0),
}


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def bd_m(ma, mb, j):
    return ma * (1 << (j - 1)) + mb


def bd_t(ta, tb, j):
    return ta * j + tb


def build_D(j, side, ma, mb, ta, tb):
    """Returns (tape dict, pos, lo, hi)."""
    m, t = bd_m(ma, mb, j), bd_t(ta, tb, j)
    assert m >= 1 and t >= 1, (m, t)
    tape, x = {}, 0
    if side == 0:                       # 1^m 0 1^t, head on rightmost 1
        for _ in range(m):
            tape[x] = 1; x += 1
        x += 1                          # the single 0 separator
        for _ in range(t):
            tape[x] = 1; x += 1
        return tape, x - 1, 0, x - 1
    else:                               # 1 0^z 1^m, head on leftmost 1
        tape[x] = 1; x += 1
        x += t                          # 0^z spacer
        for _ in range(m):
            tape[x] = 1; x += 1
        return tape, 0, 0, x - 1


def decode(tape, lo, hi, side):
    """side R: 1^m 0 1^t -> (m,t).  side L: 1 0^z 1^m -> (m,z).  None on miss."""
    cells = [tape.get(x, 0) for x in range(lo, hi + 1)]
    if len(cells) < 3:
        return None
    i = 0
    if side == 0:
        m = 0
        while i < len(cells) and cells[i] == 1:
            m += 1; i += 1
        z = 0
        while i < len(cells) and cells[i] == 0:
            z += 1; i += 1
        t = 0
        while i < len(cells) and cells[i] == 1:
            t += 1; i += 1
        if i != len(cells) or m < 1 or t < 1 or z != 1:
            return None
        return m, t
    if cells[0] != 1:
        return None
    i = 1
    z = 0
    while i < len(cells) and cells[i] == 0:
        z += 1; i += 1
    m = 0
    while i < len(cells) and cells[i] == 1:
        m += 1; i += 1
    if i != len(cells) or z < 1 or m < 1:
        return None
    return m, z


def cstr(tape, pos, lo, hi):
    out = []
    for x in range(min(lo, pos), max(hi, pos) + 1):
        c = str(tape.get(x, 0))
        out.append("[%s]" % c if x == pos else c)
    return ''.join(out)


def rle(tape, lo, hi):
    """Run-length encoding of the extent, as a compact string."""
    out, x = [], lo
    while x <= hi:
        c = tape.get(x, 0)
        n = 0
        while x + n <= hi and tape.get(x + n, 0) == c:
            n += 1
        out.append("%d^%d" % (c, n) if n > 1 else str(c))
        x += n
    return ' '.join(out)


def lap(name, j, trace=False, maxsteps=None):
    spec, edge, side, ma, mb, mdbl, ta, tb = MACHINES[name]
    tab = parse(spec)
    tape, pos, lo, hi = build_D(j, side, ma, mb, ta, tb)
    m0 = bd_m(ma, mb, j)
    st = edge
    budget = maxsteps or (400 * (m0 + 4) ** 2 + 100000)
    fired = set()
    lastd = 0
    turns = []          # (step, pos, state, dir-change)
    for n in range(budget):
        at_frontier = (st == edge and
                       ((side == 0 and pos >= hi) or (side == 1 and pos <= lo)))
        if at_frontier and n > 0:
            d = decode(tape, lo, hi, side)
            if d and d[0] > m0:
                return dict(steps=n, m=d[0], t=d[1], turns=turns,
                            fired=fired, lo=lo, hi=hi, tape=tape, pos=pos)
        sym = tape.get(pos, 0)
        fired.add((st, sym))
        e = tab[(st, sym)]
        if e is None:
            return dict(halt=True, steps=n)
        w, d, nx = e
        tape[pos] = w
        if w:
            lo = min(lo, pos); hi = max(hi, pos)
        if d != lastd and n:
            turns.append((n, pos, LAB[st], rle(tape, lo, hi)))
        lastd = d
        pos += d
        st = nx
        if pos < lo - 1 or pos > hi + 1:
            lo = min(lo, pos); hi = max(hi, pos)
        if trace and n < 400:
            print("%6d %s %s" % (n, LAB[st], cstr(tape, pos, lo, hi)))
    return dict(timeout=True, steps=budget)


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else '13'
    jmin = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    jmax = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    trace = '--trace' in sys.argv
    spec, edge, side, ma, mb, mdbl, ta, tb = MACHINES[name]
    print("#%s %s  edge=%s side=%s  m=%d*2^(j-1)%+d -> 2m%+d   t=%d*j%+d" %
          (name, spec, LAB[edge], "RL"[side], ma, mb, mdbl, ta, tb))
    prev = None
    for j in range(jmin, jmax + 1):
        m, t = bd_m(ma, mb, j), bd_t(ta, tb, j)
        r = lap(name, j, trace=trace and j == jmin)
        if r.get('halt') or r.get('timeout'):
            print("  j=%d  m=%-6d t=%-3d  FAILED %s" % (j, m, t, r))
            continue
        okm = (r['m'] == 2 * m + mdbl)
        okt = (r['t'] == t + ta)
        ratio = (r['steps'] / prev) if prev else 0.0
        print("  j=%d  m=%-6d t=%-3d -> m'=%-6d t'=%-3d  %s%s  steps=%-9d "
              "ratio=%.3f  turns=%d  fired=%d/8" %
              (j, m, t, r['m'], r['t'],
               "OK" if okm else "M-MISMATCH(exp %d)" % (2 * m + mdbl),
               "" if okt else " T-MISMATCH(exp %d)" % (t + ta),
               r['steps'], ratio, len(r['turns']), len(r['fired'])))
        prev = r['steps']
        if j == jmin:
            print("      turnarounds:")
            for (n, p, q, sh) in r['turns'][:40]:
                print("        %6d @%-4d %s  %s" % (n, p, q, sh))
            if len(r['turns']) > 40:
                print("        ... (%d total)" % len(r['turns']))


if __name__ == '__main__':
    main()
