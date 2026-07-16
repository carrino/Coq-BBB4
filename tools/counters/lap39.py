#!/usr/bin/env python3
"""Symbolic lap for #39 (1RB1RD_1LC1LB_1LD0LB_1RD0RA), mono2_counter,
prefix (1), comb (110), edge C, hoff 0.  Anchor over p = a+1 >= 3:

  C(p) = (C, [], 1, (110)^(p-1) ++ Wm2(p))

with Wm2 the interleaved-marker encoding of p (marker 1 at even
cells, bits of v = p - 2^k at odd cells LSB first, ending at the top
marker; as a positive: xH -> [1], xO q -> 1,0::Wm2 q,
xI q -> 1,1::Wm2 q).  One lap: a 7-step prologue extends the comb
region 3 cells left, a 3-step cycle crosses comb+leading marker
(110 -> rotated 101 view), a 2-step climb crosses the low set bits
of v (marker cleared, bit kept), the first clear bit is set (or the
area extends on overflow v = 2^k - 1), and the return sweep restores
markers, clears the climbed bits and rebuilds the comb one unit
longer."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB1RD_1LC1LB_1LD0LB_1RD0RA"
A, B, C, D = 0, 1, 2, 3
EDGE = C

def carry(p):
    j = 0
    while (p >> j) & 1: j += 1
    return j, (p == (1 << j) - 1)

def wm2(p):
    out = []
    while p > 1:
        out += [1, p & 1]
        p >>= 1
    return out + [1]

def C_conf(p):
    return (EDGE, [], 1, rep([1, 1, 0], p - 1) + wm2(p))

def lap(ex, p):
    ex.steps = 0
    cnt = p - 1
    j, ov = carry(p)
    cfg = C_conf(p)
    # prologue: 3 cells left, comb entry
    cfg = ex.conc(cfg, False, True, 7, None, 1, "U1")
    # crossing: comb + leading marker, rotated (101) view
    cfg = ex.cycR(cfg, 3, 3, cnt, "U2")
    if not ov:
        cfg = ex.cycR(cfg, 2, 2, j, "U3")       # climb the set bits
        cfg = ex.conc(cfg, True, True, 2, 0, 2, "U4")   # set first clear bit
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5")   # turn at next marker
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")   # keep the set bit
        cfg = ex.cycL(cfg, 2, 0, 2, j, "U7")    # restore markers, clear bits
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")   # restore W0 marker
    else:
        cfg = ex.cycR(cfg, 2, 2, j - 1, "U3")
        cfg = ex.conc(cfg, True, False, 2, 0, None, "U4e")  # set past the top
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")   # new top marker, turn
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10")  # clear the overshoot
        cfg = ex.cycL(cfg, 2, 0, 2, j - 1, "U7")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.cycL(cfg, 3, 0, 3, cnt + 1, "U9")  # comb return, one unit longer
    return ex.steps, cfg

def raw_lap(ex, p):
    cfg = C_conf(p)
    tgt = norm(C_conf(p + 1))
    for it in range(1, 400 * p + 8000):
        cfg = ex.cstep(cfg)
        if cfg[0] == EDGE and norm(cfg) == tgt:
            return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ex = Exec(SPEC)
    bad = 0
    for p in range(3, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, p)
        except (AssertionError, Wall) as e:
            print(f"p={p}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, p)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(C_conf(p + 1)))
        if not ok:
            print(f"p={p}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(C_conf(p+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"p=3..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
