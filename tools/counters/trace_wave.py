#!/usr/bin/env python3
"""Wave-counter recon tracer (mirrors verify.c wc_build/wc_pass/wc_expected).

The wave event config (side R, state = edge, head one cell right of the
rightmost 1):

    1^{B_0} 0 1^{B_1} 0 ... 0 1^{B_m}   (single-0 separators)

B_0 = lead, B_m = frontier.  Pass rule (parities only):
  out = B; out[m] += 1; scan i=m-1..0, par = B[i+1] + (poff if i==m-1 else 0),
  first odd -> out[i]+=1, class = (i==0 ? lead : m-i); else if B[0]==1 SPAWN
  (insert length-1 block after lead), else undefined.

Usage:  trace_wave.py <id> [npasses]
"""
import sys

WAVE = {  # id -> (spec, edge, side, poff, boot)
    '6':  ("1RB0LB_0LB0RC_1LD1RC_1LA1RB", 'C', 'R', 1, [1, 1, 2, 4]),
    '7':  ("1RB0LC_1LA1RD_1LA1LC_0RD1RB", 'A', 'L', 1, [1, 1, 2, 4]),
    '17': ("1RB0RD_0LB1LC_1RA1LB_1RA1RD", 'D', 'R', 0, [1, 1, 2, 3]),
    '24': ("1RB1LA_1RC1LD_1LD0RD_0RD0LA", 'A', 'L', 1, [1, 1, 2, 4]),
    '27': ("1RB1LC_1LC0RD_0LC1LA_1RB1RD", 'D', 'R', 1, [1, 1, 2, 4]),
    '36': ("1RB1RA_1LC0RA_0LC1LD_1RB1LC", 'A', 'R', 1, [1, 1, 2, 4]),
}
LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def wc_expected(B, poff):
    m = len(B) - 1
    out = list(B)
    out[m] += 1
    for i in range(m - 1, -1, -1):
        par = B[i + 1] + (poff if i == m - 1 else 0)
        if par % 2 == 1:
            out[i] += 1
            return out, (0 if i == 0 else m - i)
    if B[0] != 1:
        return out, -2
    out = out[:1] + [1] + out[1:]
    return out, -1


def build(B, side):
    """Return (tape dict, head pos, edge_from_state) for the event config."""
    tape = {}
    x = 0
    if side == 'R':
        for j in range(len(B)):
            for _ in range(B[j]):
                tape[x] = 1; x += 1
            x += 1  # separator
        return tape, x - 1
    else:  # side L: laid reversed, head one left of leftmost 1
        for jj in range(len(B)):
            j = len(B) - 1 - jj
            for _ in range(B[j]):
                tape[x] = 1; x += 1
            x += 1
        return tape, -1


def decode(tape, lo, hi, side):
    """Runs of 1 separated by single 0s -> block vector (canonical order)."""
    blocks = []
    x = lo
    while x <= hi:
        if tape.get(x, 0) == 0:
            return None
        b = 0
        while x <= hi and tape.get(x, 0) == 1:
            b += 1; x += 1
        blocks.append(b)
        if x <= hi:
            if tape.get(x, 0) != 0:
                return None
            x += 1
    if side == 'L':
        blocks = blocks[::-1]
    return blocks


def run_pass(tab, edge, side, tape, pos, verbose=False):
    """Simulate to the next event; return (next_B, class-ish, steps, minpos,
    span, firing-set, per-step list if verbose)."""
    st = edge
    # bounding box of nonzero
    nz = [k for k in tape if tape[k]]
    lo, hi = min(nz), max(nz)
    mn = pos
    fired = set()
    steps = 0
    hist = []
    for it in range(2000000):
        sym = tape.get(pos, 0)
        e = tab[(st, sym)]
        if e is None:
            return None
        fired.add((st, sym))
        w, d, ns = e
        if verbose:
            hist.append((steps, LAB[st], pos, sym, w, LAB[ns]))
        tape[pos] = w
        if w:
            lo = min(lo, pos); hi = max(hi, pos)
        else:
            if pos == lo:
                while lo <= hi and tape.get(lo, 0) == 0: lo += 1
            if pos == hi:
                while hi >= lo and tape.get(hi, 0) == 0: hi -= 1
        pos += d; st = ns; steps += 1
        mn = min(mn, pos) if side == 'R' else max(mn, pos)
        at_ev = (d > 0 and pos == hi + 1) if side == 'R' else (d < 0 and pos == lo - 1)
        if it > 0 and st == edge and lo <= hi and at_ev:
            B2 = decode(tape, lo, hi, side)
            if B2 is not None:
                anchor = lo if side == 'R' else hi
                return (B2, steps, mn, (lo, hi), anchor, fired, hist)
    return None


def main():
    tid = sys.argv[1]
    npasses = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    spec, edge_c, side, poff, boot = WAVE[tid]
    tab = parse(spec)
    edge = ord(edge_c) - ord('A')
    print(f"#{tid} {spec} edge={edge_c} side={side} poff={poff} boot={boot}")
    tape, pos = build(boot, side)
    B = list(boot)
    for k in range(npasses):
        exp, cls = wc_expected(B, poff)
        res = run_pass(tab, edge, side, dict(tape), pos)
        if res is None:
            print(f"  pass {k}: B={B} -> NO EVENT (cls={cls})"); break
        B2, steps, mn, span, anchor, fired, _ = res
        match = "OK" if B2 == exp else f"MISMATCH exp={exp}"
        firedstr = ''.join(LAB[s] + str(y) for (s, y) in sorted(fired))
        print(f"  pass {k:3d}: B={B} cls={cls:2d} steps={steps:6d} "
              f"span={span} depth={mn} -> {B2} [{match}] fired={firedstr}")
        B = B2
        tape, pos = build(B, side)


if __name__ == "__main__":
    main()
