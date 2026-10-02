"""LE7: a faster `termrun_detect.anchor_strings` (same output): the tape
is an array, and the nonzero span is kept incrementally instead of being
recomputed every step."""


def anchor_strings(spec, steps=150000):
    import termrun_detect as TD
    tm = TD.parse(spec)
    W = 1 << 16
    tape = bytearray(2 * W)
    h = W
    q = 0
    nz = 0
    lo = hi = None   # span of nonzero cells
    out = {}
    for t in range(steps):
        s = tape[h]
        tr = tm[(q, s)]
        if tr is None:
            return out
        if nz:
            if lo >= h:
                out.setdefault((q, s, 'R'), []).append(
                    ''.join('1' if c else '0' for c in tape[h + 1:hi + 1]))
            elif hi <= h:
                out.setdefault((q, s, 'L'), []).append(
                    ''.join('1' if c else '0' for c in tape[h - 1:lo - 1:-1] if True)
                    if lo > 0 else ''.join('1' if tape[i] else '0' for i in range(h - 1, lo - 1, -1)))
        w, d, nq = tr
        if w != s:
            tape[h] = w
            if w:
                nz += 1
                if lo is None or h < lo:
                    lo = h
                if hi is None or h > hi:
                    hi = h
            else:
                nz -= 1
                if nz == 0:
                    lo = hi = None
                elif h == lo:
                    while not tape[lo]:
                        lo += 1
                elif h == hi:
                    while not tape[hi]:
                        hi -= 1
        h += d
        q = nq
        if h <= 0 or h >= 2 * W - 1:
            return out
    return out
