"""visits keyed by (state, sym, side, other-side word up to K cells)"""
import sys
sys.path.insert(0, '../le3')
import termrun_detect as TD


def anchor_strings2(spec, steps, K=3):
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    lo, hi = 0, -1
    out = {}
    for _t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            return out
        while lo <= hi and not tape.get(lo, 0):
            lo += 1
        while hi >= lo and not tape.get(hi, 0):
            hi -= 1
        if hi >= lo:
            if lo >= h - K:
                o = ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)) if lo < h else ''
                out.setdefault((q, s, 'R', o), []).append(
                    ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)))
            if hi <= h + K:
                o = ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)) if hi > h else ''
                out.setdefault((q, s, 'L', o), []).append(
                    ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)))
        w, d, nq = tr
        tape[h] = w
        if w:
            if hi < lo:
                lo = hi = h
            else:
                lo, hi = min(lo, h), max(hi, h)
        h += d
        q = nq
    return out


if __name__ == '__main__':
    A = anchor_strings2(sys.argv[1], int(sys.argv[2]))
    for k in sorted(A, key=lambda k: -len(A[k]))[:8]:
        v = A[k]
        print(k, len(v), v[-3:])
