#!/usr/bin/env python3
"""Symbolic lap for #4 (1RB0LA_1LC1RC_1RD1LB_1LA0RD), exp_counter side L,
edge C, moff 0.  Mirror geometry of #2: W side on the LEFT (bit i at
-2(i+1)), marker side on the RIGHT encoding v itself (bit b at
+(3(b+1)+1)); anchor cells 0 and +1 are 1.  As a cconf:

    (C, l = Wp(v), h = 1, r = 1 :: 0 :: 0 :: Gp(v))

with Gp(p) the marker-FIRST stride-3 groups [b0, 0,0, b1, 0,0, ...]
(r = 1 :: Tp(v) in zeros-first terms).  With moff 0 both sides carry
the same run length j = trailing_ones(v).  One lap: leftward 2-step
cycle over the set bits, 4-step flip, rightward 1-step D-run zeroing,
4-step marker junction, 5-step strides over set markers, 2-step stop
(the overflow spelling crosses the last marker at the blank edge),
1-step A-walk zeroing back, 3-step rebuild."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0LA_1LC1RC_1RD1LB_1LA0RD"
A, B, C, D = 0, 1, 2, 3

def Wp(v):
    out = []
    while v:
        out += [0, v & 1]
        v >>= 1
    return out

def Gp(v):
    out = []
    while v:
        out += [v & 1, 0, 0]
        v >>= 1
    return out[:-2]  # drop the trailing two zeros of the last group

def carry(v):
    j = 0
    while (v >> j) & 1: j += 1
    return j, (v == (1 << j) - 1)

def C_conf(v):
    return (C, Wp(v), 1, [1, 0, 0] + Gp(v))

def lap(ex, v):
    ex.steps = 0
    j, ov = carry(v)
    cfg = C_conf(v)

    # ---- W side (left): binary +1 ----
    cfg = ex.cycL(cfg, 2, 0, 2, j, "UWout")          # cross set bits
    if not ov:
        cfg = ex.conc(cfg, True, True, 4, 2, 0, "UWf")   # flip clear bit
    else:
        cfg = ex.conc(cfg, False, True, 4, None, 0, "UWfE")
    cfg = ex.cycR(cfg, 1, 1, 2 * j + 1, "UWb")       # D-run zeroing

    # ---- marker side (right): binary +1 ----
    cfg = ex.conc(cfg, True, True, 4, 0, 2, "UJ")    # junction into groups
    if not ov:
        cfg = ex.cycR(cfg, 3, 5, j, "UMs")           # strides over set markers
        cfg = ex.conc(cfg, True, True, 2, 0, 1, "UMi")   # interior stop
    else:
        cfg = ex.cycR(cfg, 3, 5, j - 1, "UMs")
        cfg = ex.conc(cfg, True, False, 5, 0, None, "UMsE")  # edge stride
        cfg = ex.conc(cfg, True, False, 2, 0, None, "UMo")   # stop at edge
    cfg = ex.cycL(cfg, 1, 0, 1, 3 * j + 2, "UAw")    # A-walk zeroing
    cfg = ex.conc(cfg, True, True, 3, 1, 0, "UEnd")  # rebuild anchor
    return ex.steps, cfg

def raw_lap(ex, v):
    cfg = C_conf(v)
    for it in range(1, 100 * v.bit_length() + 4000):
        cfg = ex.cstep(cfg)
        if norm(cfg) == norm(C_conf(v + 1)):
            return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ex = Exec(SPEC)
    bad = 0
    for v in range(1, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, v)
        except (AssertionError, Wall) as e:
            print(f"v={v}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, v)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(C_conf(v + 1)))
        if not ok:
            print(f"v={v}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(C_conf(v+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"v=1..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
