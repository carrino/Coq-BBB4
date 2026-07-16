#!/usr/bin/env python3
"""Parametric lap tracer for the mono_counter family (#26, #31).

Prints turnaround summaries + sweep-boundary snapshots so the phase
structure can be read off, exactly as done for #10.
"""
import sys

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

MACHINES = {
    '26': ("1RB1LC_0LC0RB_1RD1LA_1RB0LA", 0, -1),   # edge A, hoff -1
    '31': ("1RB1LD_1RC0RB_0LA1RB_0LD1LA", 1, +1),   # edge B, hoff +1
    '10': ("1RB0LD_0LC0RB_1RA1LD_1RB1LC", 2, 0),
}
LAB = "ABCD"

def encode_odd(a):
    k = a.bit_length() - 1
    cells = [0] * (2 * (k + 1))
    for i in range(k + 1):
        if (a >> i) & 1: cells[2*i+1] = 1
    return cells

def build_C(a):
    tape = {}
    for i in range(a):
        tape[3*i] = 1; tape[3*i+1] = 1
    for i, c in enumerate(encode_odd(a)):
        if c: tape[3*a+i] = c
    return tape

def cstr(tape, pos, lo, hi):
    out = []
    for x in range(min(lo, pos), max(hi, pos)+1):
        c = str(tape.get(x, 0))
        out.append(f"[{c}]" if x == pos else c)
    return ''.join(out)

def run(name, a, mode="turns"):
    spec, edge, hoff = MACHINES[name]
    tab = parse(spec)
    tape = build_C(a)
    pos, st = hoff, edge
    lo = 0; hi = max(x for x in tape if tape[x])
    lastd = 0
    turns = []
    visited = set()
    hist = []
    for n in range(4000*a + 40000):
        sym = tape.get(pos, 0)
        visited.add(st)
        e = tab[(st, sym)]
        if e is None:
            print("HALT"); return
        w, d, ns = e
        if lastd and d != lastd:
            turns.append((n, pos, LAB[st]))
        lastd = d
        hist.append((n, pos, st, cstr(tape, pos, lo, hi)))
        tape[pos] = w
        if w:
            lo = min(lo, pos); hi = max(hi, pos)
        else:
            if pos == lo:
                while lo <= hi and tape.get(lo, 0) == 0: lo += 1
            if pos == hi:
                while hi >= lo and tape.get(hi, 0) == 0: hi -= 1
        pos += d; st = ns
        # event check
        if st == edge and pos <= lo + hoff:
            cs = lo; aa = 0
            while all(tape.get(cs+3*aa+q, 0) == (1,1,0)[q] for q in range(3)) and cs+3*aa+2 <= hi:
                aa += 1
            if aa > a:
                ws = cs + 3*aa
                cells = [tape.get(ws+i, 0) for i in range(hi-ws+1)]
                val = 0; ok = True
                for p2, c in enumerate(cells):
                    if p2 % 2 == 0:
                        if c: ok = False; break
                    elif c: val |= 1 << (p2//2)
                if ok and val == aa:
                    print(f"#{name} a={a}: lap={n+1} steps, states={sorted(LAB[s] for s in visited)}, "
                          f"final pos={pos} comb_start={cs}, turns={len(turns)}")
                    if mode == "turns":
                        # extremal turns only: local max/min positions
                        ext = []
                        for i, (tn, tp, tst) in enumerate(turns):
                            nbr = [turns[k][1] for k in (i-1, i+1) if 0 <= k < len(turns)]
                            if all(tp >= x for x in nbr) or all(tp <= x for x in nbr):
                                ext.append((tn, tp, tst))
                        # keep global-scale ones
                        big = [t for t in ext if abs(t[1]) > a or t[1] < 2]
                        print("   extremal:", [t for t in ext if not (2 <= t[1] <= 3*a - 2)])
                    elif mode == "full":
                        for h2 in hist: print(f"  {h2[0]:5d} {LAB[h2[2]]} p={h2[1]:4d} {h2[3]}")
                    return n+1

if __name__ == "__main__":
    name = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].isdigit() else "turns"
    a_list = [int(x) for x in sys.argv[2:] if x.isdigit()] or [6]
    for a in a_list:
        run(name, a, mode)
