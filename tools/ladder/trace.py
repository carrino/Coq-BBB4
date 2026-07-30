#!/usr/bin/env python3
"""UNTRUSTED: concrete simulation + block-RLE snapshots for ladder mining."""

from engine import Expr, canon_run


def simulate(tm, steps, snap_every=1, max_snap=200000):
    tape = {}
    pos = 0
    q = 0
    lo = hi = 0
    out = []
    for t in range(steps):
        h = tape.get(pos, 0)
        tr = tm.get((q, h))
        if tr is None:
            out.append((t, None))
            return out
        if t % snap_every == 0 and len(out) < max_snap:
            out.append((t, snapshot(tape, pos, q, lo, hi)))
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        lo = min(lo, pos)
        hi = max(hi, pos)
        q = q2
    return out


def snapshot(tape, pos, q, lo, hi):
    h = tape.get(pos, 0)
    L = block_rle([tape.get(i, 0) for i in range(pos - 1, lo - 1, -1)])
    R = block_rle([tape.get(i, 0) for i in range(pos + 1, hi + 1)])
    return (q, h, L, R)


def block_rle(cells, maxb=6):
    """Greedy near-end-first block RLE.  At each position pick the (b, k)
    with k >= 2 maximizing coverage b*k (ties: smaller b); else emit one
    cell.  Uniform stretches collapse to unit runs."""
    # strip far blanks
    n = len(cells)
    while n and cells[n - 1] == 0:
        n -= 1
    cells = cells[:n]
    out = []
    i = 0
    while i < n:
        best = None
        for b in range(1, maxb + 1):
            if i + b > n:
                break
            w = tuple(cells[i:i + b])
            k = 1
            while i + b * (k + 1) <= n and \
                    tuple(cells[i + b * k:i + b * (k + 1)]) == w:
                k += 1
            if k >= 2 or b == 1:
                cov = b * k
                if best is None or cov > best[0]:
                    best = (cov, b, k, w)
        cov, b, k, w = best
        if b == 1:
            # extend uniform stretch fully
            s = cells[i]
            j = i
            while j < n and cells[j] == s:
                j += 1
            out.append(((s,), Expr(j - i)))
            i = j
        else:
            out.append(canon_run(w, Expr(k)))
            i += b * k
    # merge adjacent equal words
    merged = []
    for w, e in out:
        if merged and merged[-1][0] == w:
            merged[-1] = (w, merged[-1][1] + e)
        else:
            merged.append((w, e))
    return tuple(merged)


def to_symbolic(snap):
    return snap


def cfg_of_snap(snap):
    return snap
