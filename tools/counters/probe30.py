#!/usr/bin/env python3
"""Probe candidate unit runs for #30 against the real machine."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, LAB
SPEC = "1RB1LD_1RC0LA_1RD0RD_1LB1RB"
A, B, C, D = 0, 1, 2, 3

ex = Exec(SPEC)
def try_unit(name, bl, br, q, l, h, r, n):
    try:
        out = ex.wsteps(bl, br, q, list(l), h, list(r), n)
        fe = f"({LAB[q]},{list(l)},{h},{list(r)})"
        fo = f"({LAB[out[0]]},{list(out[1])},{out[2]},{list(out[3])})"
        print(f"{name:6s} bl={int(bl)} br={int(br)} n={n}: {fe} -> {fo}")
    except Wall as e:
        print(f"{name:6s} bl={int(bl)} br={int(br)} n={n}: WALL {e}")

# mission-claimed units:
try_unit("UTe", True, False, B, [], 0, [], 3)          # (B,([],0,[]))->3 ->(B,([1],1,[1]))?
try_unit("wig", True, True, B, [1,1], 1, [], 5)        # cycLW (B,([1;1],1,[]))->(B,([1],1,[0]))?
try_unit("wig2", True, True, D, [1], 1, [], 3)
try_unit("UJ",  True, True, B, [1,0], 1, [], 2)        # (B,([1;0],1,[]))->2->(D,([],0,[1;0]))?
try_unit("UC",  True, True, D, [1,1,0], 0, [], 3)      # (D,([1;1;0],0,[]))->3->(D,([],0,[1;0;1]))?
try_unit("US",  True, True, B, [], 0, [1,1,0], 3)      # (B,([],0,[1;1;0]))->3->(B,([1;0;1],0,[]))?
# a few exploratory
for n in range(1,7):
    try_unit(f"eT{n}", True, False, B, [], 0, [], n)
print("---")
for n in range(1,7):
    try_unit(f"eA{n}", True, True, A, [1], 1, [], n)
