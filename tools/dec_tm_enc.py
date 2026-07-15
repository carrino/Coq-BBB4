#!/usr/bin/env python3
"""Decode Census/Decide.v tm_enc positives back to machine text.

tm_enc = N.succ_pos (fold_left (fun acc o => 17*acc + slot_code o)
                     [A0;A1;B0;B1;C0;C1;D0;D1] 0)
slot_code None = 0; Some(w,d,nx) = 1 + w + 2*dir(DL=0,DR=1) + 4*st.

Usage: dec_tm_enc.py N [N ...]   (the printed positive values)
"""
import sys

def dec_slot(c):
    if c == 0:
        return '---'
    c -= 1
    w, d, st = c & 1, (c >> 1) & 1, c >> 2
    return f"{w}{'R' if d else 'L'}{chr(65 + st)}"

def dec(v):
    v -= 1          # N.succ_pos
    slots = []
    for _ in range(8):
        slots.append(v % 17)
        v //= 17
    slots.reverse()
    return '_'.join(dec_slot(slots[2*i]) + dec_slot(slots[2*i+1])
                    for i in range(4))

for a in sys.argv[1:]:
    print(dec(int(a.rstrip('%positive').strip())))
