#!/usr/bin/env python3
"""Symbolic lap for #2 (1RB0LA_1LC0RB_1RD1LD_1LA1RC), exp_counter side R,
edge D, moff 1.  Anchor C(v): head cell 0 = 1 (state D), cell -1 = 1,
W side (right) = v in binary LSB-first at even cells (bit i at 2(i+1),
fillers 0), marker side (left) = v+1 as stride-3 markers (bit b at
-(3(b+1)+1)).  As a cconf:

    (D, l = 1 :: Tp(v+1), h = 1, r = Wp(v))

with Wp as in MonoCounter and Tp(p) the zeros-first stride-3 groups
[0,0,b0, 0,0,b1, ...].  One lap = W-side binary +1 (rightward 2-step
cycle over set bits, flip, 1-step walk-back zeroing) then marker-side
binary +1 (5-step bounce strides over set markers, 8-step stop setting
the clear/fresh marker, 1-step B-run zeroing, 3-step rebuild)."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0LA_1LC0RB_1RD1LD_1LA1RC"
A, B, C, D = 0, 1, 2, 3

def Wp(v):
    out = []
    while v:
        out += [0, v & 1]
        v >>= 1
    return out

def Tp(v):
    out = []
    while v:
        out += [0, 0, v & 1]
        v >>= 1
    return out

def carry(v):
    j = 0
    while (v >> j) & 1: j += 1
    return j, (v == (1 << j) - 1)

def C_conf(v):
    return (D, [1] + Tp(v + 1), 1, Wp(v))

def lap(ex, v):
    ex.steps = 0
    j, ovW = carry(v)            # W-side carry
    jm, ovM = carry(v + 1)       # marker-side carry
    cfg = C_conf(v)

    # ---- W side: binary +1 ----
    cfg = ex.cycR(cfg, 2, 2, j, "UWout")            # cross set bits
    if not ovW:
        cfg = ex.conc(cfg, True, True, 4, 0, 2, "UWf")   # flip clear bit
    else:
        cfg = ex.conc(cfg, True, False, 4, 0, None, "UWfE")  # flip at edge
    cfg = ex.cycL(cfg, 1, 0, 1, 2 * j + 1, "UWb")   # walk-back zeroing

    # ---- marker side: binary +1 ----
    cfg = ex.cycL(cfg, 3, 0, 5, jm, "UMs")          # strides over set markers
    if not ovM:
        cfg = ex.conc(cfg, True, True, 8, 3, 0, "UMi")   # interior stop
    else:
        cfg = ex.conc(cfg, False, True, 8, None, 0, "UMo")  # stop at edge
    cfg = ex.cycR(cfg, 1, 1, 3 * jm, "UBr")         # B-run zeroing
    cfg = ex.conc(cfg, True, True, 3, 0, 1, "UEnd") # rebuild anchor
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
