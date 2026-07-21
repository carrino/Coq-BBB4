#!/usr/bin/env python3
"""Recon: segment #9's lap into macro-phases; RLE at each turnaround.
Anchor D(j) = (10)^kg 1^acc, head on rightmost 1, state D."""
import sys
sys.path.insert(0, '.')
from executor import Exec, LAB

SPEC = "1RB0LC_1RC0RD_1LA0LC_1RD0RA"
A, B, C, D = 0, 1, 2, 3
EDGE = D

def anchor(j):
    kg = (1 << j) - 1
    acc = 3 * j
    return [1, 0] * kg + [1] * acc, kg, acc

def run(j, maxstep=200000, verbose=True):
    tab = Exec(SPEC).tab
    cells, kg, acc = anchor(j)
    tape = {i: c for i, c in enumerate(cells) if c}
    lo, hi = 0, len(cells) - 1
    pos = hi                  # rightmost 1
    st = EDGE
    lastd = 0
    events = []
    def emit(tag):
        L = min(lo, pos); R = max(hi, pos)
        arr = [tape.get(x, 0) for x in range(L, R + 1)]
        events.append((tag, st, pos, pos - L, arr))
    for it in range(maxstep):
        sym = tape.get(pos, 0)
        e = tab[(st, sym)]
        if e is None:
            print("HALT"); return
        w, d, ns = e
        if lastd == -1 and d == +1: emit("Lturn")
        if lastd == +1 and d == -1: emit("Rturn")
        lastd = d
        tape[pos] = w
        if w:
            lo = min(lo, pos); hi = max(hi, pos)
        else:
            if pos == lo:
                while lo <= hi and tape.get(lo, 0) == 0: lo += 1
            if pos == hi:
                while hi >= lo and tape.get(hi, 0) == 0: hi -= 1
        pos += d; st = ns
        if st == EDGE and pos >= hi and it > 5:
            kg2, acc2 = 2 * kg + 1, acc + 3
            arr = [tape.get(lo + i, 0) for i in range(hi - lo + 1)]
            if arr == [1, 0] * kg2 + [1] * acc2 and pos == hi:
                emit("DONE")
                break
    if verbose:
        for tag, s, p, hp, arr in events:
            out = []
            i = 0
            while i < len(arr):
                jj = i
                while jj < len(arr) and arr[jj] == arr[i]: jj += 1
                n = jj - i
                mark = "*" if i <= hp < jj else ""
                out.append(f"{arr[i]}^{n}{mark}" if n > 1 else f"{arr[i]}{mark}")
                i = jj
            print(f"{tag:6s} {LAB[s]} p={p:4d} hp={hp:3d}  {' '.join(out)}")
    return events

if __name__ == "__main__":
    js = [int(x) for x in sys.argv[1:]] or [2]
    for j in js:
        c, kg, acc = anchor(j)
        print(f"===== j={j} kg={kg} acc={acc} =====")
        run(j)
