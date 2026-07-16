#!/usr/bin/env python3
"""Symbolic lap for #38 (1RB1RD_1LC1LB_0LD0LB_1RD0RA), mono2_counter,
prefix (1), comb (011), edge B, hoff 0, comb_step 2, base_a 1.
Anchor over p = a+1 >= 3:

  C(p) = (B, [], 1, (011)^(2p-1) ++ Wm2(p))

Same interleaved-marker working area as #39 (the machines share the
A/B/D rows and differ only in C0), but the comb grows by TWO units
per lap, so the lap is two out-and-back sweeps: sweep 1 crosses the
comb, does the v-increment on the working area and returns,
extending the comb region 3 cells left; sweep 2 re-crosses, rebuilds
the comb phase at the working-area junction and returns, extending
another 3 cells."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB1RD_1LC1LB_0LD0LB_1RD0RA"
A, B, C, D = 0, 1, 2, 3
EDGE = B

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
    return (EDGE, [], 1, rep([0, 1, 1], 2 * p - 1) + wm2(p))

def lap(ex, p):
    ex.steps = 0
    cnt = 2 * p - 1
    j, ov = carry(p)
    cfg = C_conf(p)
    # ---- sweep 1: prologue, crossing, increment, return ----
    cfg = ex.conc(cfg, False, True, 7, None, 1, "UP1")
    cfg = ex.cycR(cfg, 3, 3, cnt - 1, "U2")
    cfg = ex.conc(cfg, True, True, 3, 0, 3, "U2b")
    if not ov:
        cfg = ex.cycR(cfg, 2, 2, j, "U3")
        cfg = ex.conc(cfg, True, True, 2, 0, 2, "U4")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")
        cfg = ex.cycL(cfg, 2, 0, 2, j, "U7")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    else:
        cfg = ex.cycR(cfg, 2, 2, j - 1, "U3")
        cfg = ex.conc(cfg, True, False, 2, 0, None, "U4e")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10")
        cfg = ex.cycL(cfg, 2, 0, 2, j - 1, "U7")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10b")
    cfg = ex.cycL(cfg, 3, 0, 3, cnt - 1, "Ur1")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10b")
    # ---- sweep 2: prologue, re-crossing, comb rebuild, return ----
    cfg = ex.conc(cfg, False, True, 4, None, 0, "UP2")
    cfg = ex.cycR(cfg, 3, 3, cnt + 1, "U2")
    cfg = ex.conc(cfg, True, True, 3, 0, 3, "U2c")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U5")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10b")
    cfg = ex.cycL(cfg, 3, 0, 3, cnt, "Ur1")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U8")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U10b")
    return ex.steps, cfg

def raw_lap(ex, p):
    cfg = C_conf(p)
    tgt = norm(C_conf(p + 1))
    for it in range(1, 800 * p + 16000):
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
