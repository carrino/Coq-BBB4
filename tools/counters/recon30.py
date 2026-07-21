#!/usr/bin/env python3
"""Recon: segment #30's lap into macro-phases by printing the config at
each left-edge / right-frontier turnaround. Compressed run-length view."""
import sys
sys.path.insert(0, '.')
from executor import Exec, LAB

SPEC = "1RB1LD_1RC0LA_1RD0RD_1LB1RB"
A, B, C, D = 0, 1, 2, 3
EDGE = B

def comb(k, t):
    # D(j): 1 0 (110)^k 1^t, head one blank right of frontier, state B.
    return [1, 0] + [1, 1, 0] * k + [1] * t

def rle(cells, lo, hi):
    # compressed run-length of cells[lo..hi]
    s = []
    i = lo
    while i <= hi:
        j = i
        while j <= hi and cells[j] == cells[i]:
            j += 1
        n = j - i
        s.append(f"{cells[i]}^{n}" if n > 1 else f"{cells[i]}")
        i = j
    return " ".join(s)

def run(j, maxstep=200000, verbose=True):
    tab = Exec(SPEC).tab
    k = (1 << j) - 1
    t = 3 * j + 4
    cells = comb(k, t)
    tape = {i: c for i, c in enumerate(cells) if c}
    lo, hi = 0, len(cells) - 1
    pos = hi + 1              # blank right of frontier
    st = EDGE
    lastd = 0
    events = []
    def emit(tag):
        L = min(lo, pos); R = max(hi, pos)
        arr = [tape.get(x, 0) for x in range(L, R + 1)]
        hp = pos - L
        events.append((tag, st, pos, hp, arr))
    for it in range(maxstep):
        sym = tape.get(pos, 0)
        # detect frontier return event (right)
        if it > 0 and st == EDGE and pos > hi:
            emit(f"RF")
            # decode?
        e = tab[(st, sym)]
        if e is None:
            print("HALT"); return
        w, d, ns = e
        # turnaround detection at extremes
        if lastd == -1 and d == +1:
            # was moving left, now right: a LEFT turnaround at pos
            emit("Lturn")
        if lastd == +1 and d == -1:
            emit("Rturn")
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
        # stop at next right frontier event decoding as D(j+1)
        if st == EDGE and pos > hi and it > 5:
            k2 = 2 * k + 1
            arr = [tape.get(lo + i, 0) for i in range(hi - lo + 1)]
            if arr == comb(k2, t + 3):
                emit("DONE")
                break
    if verbose:
        for tag, s, p, hp, arr in events:
            # rle of arr
            out = []
            i = 0
            while i < len(arr):
                jj = i
                while jj < len(arr) and arr[jj] == arr[i]:
                    jj += 1
                n = jj - i
                mark = "*" if i <= hp < jj else ""
                out.append(f"{arr[i]}^{n}{mark}" if n > 1 else f"{arr[i]}{mark}")
                i = jj
            print(f"{tag:6s} {LAB[s]} p={p:4d} hp={hp:3d}  {' '.join(out)}")
    return events

if __name__ == "__main__":
    js = [int(x) for x in sys.argv[1:]] or [2]
    for j in js:
        print(f"===== j={j} k={(1<<j)-1} t={3*j+4} =====")
        run(j)
