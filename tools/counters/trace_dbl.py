#!/usr/bin/env python3
"""Trace double_counter #9/#30/#32/#37 and blockdbl #11/#13/#28."""
import sys

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

LAB = "ABCD"

# name: (spec, edge, build(j) -> (cells, headpos 'L'/'R'), decode-check via build)
def b30(j):
    k = (1 << j) - 1
    t = 4 + 3 * j
    return [1, 0] + [1, 1, 0] * k + [1] * t, 'R+1'

def b9(j):
    kg = (1 << j) - 1
    acc = 3 * j
    return [1, 0] * kg + [1] * acc, 'R'

def b32(j):
    kg = 1 << j
    acc = 3 + 2 * j
    return [1] + [1, 1, 0] * kg + [0] * acc + [1], 'R'

def b37(j):
    k = (1 << j) - 1
    t = 1 + 3 * j
    return [1] * t + [0] + [1, 1, 0] * k + [1], 'L'

def b11(j):
    m = 3 * (1 << (j - 1)) + 1
    t = 2 * j - 1
    return [1] * m + [0] + [1] * t, 'R'

def b13(j):
    m = 3 * (1 << (j - 1))
    t = 2 * j - 1
    return [1] * m + [0] + [1] * t, 'R'

def b28(j):
    m = 4 * (1 << (j - 1)) - 1
    z = 2 * j
    return [1] + [0] * z + [1] * m, 'L'

MACHINES = {
    '30': ("1RB1LD_1RC0LA_1RD0RD_1LB1RB", 1, b30),
    '9':  ("1RB0LC_1RC0RD_1LA0LC_1RD0RA", 3, b9),
    '32': ("1RB1LD_1RC0RB_1LA0RC_0LD0LA", 1, b32),
    '37': ("1RB1RB_1RC1LC_1LD0RA_1LB0LB", 1, b37),
    '11': ("1RB0LD_1RC0RC_1LA1RB_0LC0LD", 2, b11),
    '13': ("1RB0RB_1LC1RA_1RA0LD_0LB0LD", 1, b13),
    '28': ("1RB1LC_1LC1RD_1LA0LC_0RD0RB", 2, b28),
}

def run(name, j, mode="turns"):
    spec, edge, build = MACHINES[name]
    tab = parse(spec)
    cells, side = build(j)
    tape = {i: c for i, c in enumerate(cells) if c}
    lo, hi = 0, len(cells) - 1
    while tape.get(hi, 0) == 0: hi -= 1
    while tape.get(lo, 0) == 0: lo += 1
    if side == 'R': pos = hi
    elif side == 'R+1': pos = hi + 1
    else: pos = lo
    st = edge
    lastd = 0
    turns = []
    hist = []
    want, _ = build(j + 1)
    while want and want[-1] == 0: want.pop()
    w0 = 0
    while want[w0] == 0: w0 += 1
    want = want[w0:]
    for it in range(400000):
        sym = tape.get(pos, 0)
        e = tab[(st, sym)]
        if e is None:
            print("HALT"); return
        w, d, ns = e
        if lastd and d != lastd:
            turns.append((it, pos, LAB[st]))
        lastd = d
        if mode == "full":
            disp = ''.join(f"[{tape.get(x,0)}]" if x == pos else str(tape.get(x,0))
                           for x in range(min(lo, pos), max(hi, pos) + 1))
            hist.append((it, pos, st, disp))
        tape[pos] = w
        if w:
            lo = min(lo, pos); hi = max(hi, pos)
        else:
            if pos == lo:
                while lo <= hi and tape.get(lo, 0) == 0: lo += 1
            if pos == hi:
                while hi >= lo and tape.get(hi, 0) == 0: hi -= 1
        pos += d; st = ns
        if st == edge and ((side in ('R', 'R+1') and pos >= hi) or (side == 'L' and pos <= lo)):
            got = [tape.get(lo + i, 0) for i in range(hi - lo + 1)]
            if got == want:
                okpos = (side == 'R' and pos == hi) or (side == 'R+1' and pos == hi + 1) \
                        or (side == 'L' and pos == lo)
                if okpos:
                    print(f"#{name} j={j}: lap={it+1} steps, turns={len(turns)}")
                    if mode == "turns":
                        print("   turns:", turns[:30])
                    elif mode == "full":
                        for h in hist:
                            print(f"  {h[0]:5d} {LAB[h[2]]} p={h[1]:4d} {h[3]}")
                    return it + 1
    print(f"#{name} j={j}: no event found")

if __name__ == "__main__":
    name = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].isdigit() else "turns"
    j_list = [int(x) for x in sys.argv[2:] if x.isdigit()] or [3]
    for j in j_list:
        run(name, j, mode)
