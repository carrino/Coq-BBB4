#!/usr/bin/env python3
"""Symbolic lap for #19 (1RB0RD_1LC0LB_1RA0LB_1RD0RC), gray_counter,
edge C, hoff -1, comb (1 0).  Anchor over the counter k >= 3 (n = k+2
comb units):

  S(k) = (C, [], 0, rep [1,0] (k+2) ++ [0] ++ Wg(k))

where Wg(k) encodes G = gray(k) = k xor (k>>1) as 3-cell slots
[bit,0,0] (LSB first), trimmed at the top marker [1].  One lap flips
slot j of the gray code (j = number of low set bits of k) and grows
the comb by one unit; the anchor drifts one cell left per lap.

Case analysis (j, ov = carry(k); note k even <=> n even <=> j = 0):
  n=2c   (j=0):    U2^c U3e_b {U4s U5s | UB1^2} U5b0 Uret^(2c-1) U6e
  n=2c+1 int j>=1: U2^c U3o UDf^(3j') U7i U3e_b {U4s U5s | UB1^2}
                   U5b0 U4s U5s UB1^(3j') U5b0 Uret^(2c) U6e
  n=2c+1 overflow: U2^c U3o UDf^(3j') U7e U8e U4s U5s
                   U5b0 U4s U5s UB1^(3j') U5b0 Uret^(2c) U6e
with j' = j-1 and b the pre-flip slot-j bit (overflow: blank = set)."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0RD_1LC0LB_1RA0LB_1RD0RC"
A, B, C, D = 0, 1, 2, 3

def gray(k): return k ^ (k >> 1)

def carry(k):
    j = 0
    while (k >> j) & 1: j += 1
    return j, (k == (1 << j) - 1)

def wg(k):
    """slot cells of gray(k), trimmed at the top marker."""
    G = gray(k)
    hb = G.bit_length() - 1
    out = []
    for i in range(hb):
        out += [(G >> i) & 1, 0, 0]
    return out + [1]

def S_conf(k):
    return (C, [], 0, rep([1, 0], k + 2) + [0] + wg(k))

def lap(ex, k):
    ex.steps = 0
    n = k + 2
    j, ov = carry(k)
    cfg = S_conf(k)
    c = n // 2
    cfg = ex.cycR(cfg, 4, 4, c, "U2")
    if n % 2 == 0:
        # j = 0: flip slot 0 right at the comb end
        b = gray(k) & 1
        cfg = ex.conc(cfg, True, True, 2, 0, 2, f"U3e{b}")
        if b == 0:
            cfg = ex.conc(cfg, True, True, 1, 1, 0, "U4s")
            cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5s")
        else:
            cfg = ex.cycL(cfg, 1, 0, 1, 2, "UB1")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5b0")
        cfg = ex.cycL(cfg, 2, 0, 2, 2 * c - 1, "Uret")
    else:
        # j >= 1: D-run to the first marker, flip slot j behind it
        jp = j - 1
        cfg = ex.conc(cfg, True, True, 3, 0, 3, "U3o")
        cfg = ex.cycR(cfg, 1, 1, 3 * jp, "UDf")
        if not ov:
            b = (gray(k) >> j) & 1
            cfg = ex.conc(cfg, True, True, 2, 0, 2, "U7i")
            cfg = ex.conc(cfg, True, True, 2, 0, 2, f"U3e{b}")
            if b == 0:
                cfg = ex.conc(cfg, True, True, 1, 1, 0, "U4s")
                cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5s")
            else:
                cfg = ex.cycL(cfg, 1, 0, 1, 2, "UB1")
        else:
            cfg = ex.conc(cfg, True, False, 2, 0, None, "U7e")
            cfg = ex.conc(cfg, True, False, 2, 0, None, "U8e")
            cfg = ex.conc(cfg, True, True, 1, 1, 0, "U4s")
            cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5s")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5b0")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U4s")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5s")
        cfg = ex.cycL(cfg, 1, 0, 1, 3 * jp, "UB1")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5b0")
        cfg = ex.cycL(cfg, 2, 0, 2, 2 * c, "Uret")
    cfg = ex.conc(cfg, False, True, 3, None, 0, "U6e")
    return ex.steps, cfg

def raw_lap(ex, k):
    cfg = S_conf(k)
    tgt = norm(S_conf(k + 1))
    for it in range(1, 400 * k + 8000):
        cfg = ex.cstep(cfg)
        if cfg[0] == C and norm(cfg) == tgt:
            return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ex = Exec(SPEC)
    bad = 0
    for k in range(3, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, k)
        except (AssertionError, Wall) as e:
            print(f"k={k}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, k)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(S_conf(k + 1)))
        if not ok:
            print(f"k={k}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(S_conf(k+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"k=3..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
