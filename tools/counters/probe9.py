#!/usr/bin/env python3
"""Probe #9 unit runs."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, LAB
SPEC = "1RB0LC_1RC0RD_1LA0LC_1RD0RA"
A, B, C, D = 0, 1, 2, 3
ex = Exec(SPEC)
def U(name, bl, br, q, l, h, r, n):
    try:
        o = ex.wsteps(bl, br, q, list(l), h, list(r), n)
        print(f"{name:8s} bl={int(bl)} br={int(br)} n={n}: ({LAB[q]},{list(l)},{h},{list(r)}) -> ({LAB[o[0]]},{list(o[1])},{o[2]},{list(o[3])})")
    except Wall as e:
        print(f"{name:8s} bl={int(bl)} br={int(br)} n={n}: WALL {e}")

# edge poke: D on rightmost 1, r=[] (blank right). Explore.
for n in range(1,9): U(f"poke{n}", True, False, D, [], 1, [], n)
print("--- collapse (leftward, A over comb 10) ---")
for n in range(1,5): U(f"colC{n}", True, True, A, [1,0], 1, [], n)
for n in range(1,5): U(f"colA{n}", True, True, A, [0,1], 1, [], n)
print("--- spread (rightward, over collapsed comb) ---")
for n in range(1,6): U(f"spr{n}", True, True, B, [], 1, [0,1], n)
for n in range(1,6): U(f"sprD{n}", True, True, D, [], 0, [1,0], n)
print("--- left edge turn ---")
for n in range(1,5): U(f"let{n}", False, True, A, [], 0, [1], n)
