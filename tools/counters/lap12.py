#!/usr/bin/env python3
"""Symbolic lap for #12 (1RB0RA_1LC1RD_1LD0LC_1RA1LB), exp_counter sym 1,
edge A.  The SYMMETRIC marker counter: stride-3 markers of v on BOTH
sides of a 4-cell anchor (cells -1,0 = 1, +1 = 0, +2 = 1); set bit b
of v as markers at -(3b+4) and +(3b+5).  As a cconf:

    (A, l = 1 :: Tp(v), h = 1, r = 0 :: 1 :: Tp(v))

(Tp zeros-first as in lap2; the left side in marker-first terms is
1 :: 0 :: 0 :: Gp(v)).  Both sides carry the same run j =
trailing_ones(v).  One lap: rightward marker +1 (3-step strides over
set markers, 4-step stop, 1-step C-run zeroing back), then leftward
marker +1 (4-step launch, 3-step strides, 2-step stop, 1-step
A-return zeroing, 6-step anchor rebuild)."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0RA_1LC1RD_1LD0LC_1RA1LB"
A, B, C, D = 0, 1, 2, 3

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
    return (A, [1] + Tp(v), 1, [0, 1] + Tp(v))

def lap(ex, v):
    ex.steps = 0
    j, ov = carry(v)
    cfg = C_conf(v)

    # ---- right side: marker +1 ----
    cfg = ex.conc(cfg, True, True, 2, 0, 2, "U1")     # into the anchor pair
    cfg = ex.cycR(cfg, 3, 3, j, "URs")                # strides over set markers
    if not ov:
        cfg = ex.conc(cfg, True, True, 4, 0, 3, "URi")    # interior stop
    else:
        cfg = ex.conc(cfg, True, False, 4, 0, None, "URo")  # stop at blank edge
    cfg = ex.cycL(cfg, 1, 0, 1, 3 * j + 3, "UCr")     # C-run zeroing back

    # ---- left side: marker +1 ----
    cfg = ex.conc(cfg, True, True, 4, 4, 0, "UL")     # launch into groups
    if not ov:
        cfg = ex.cycL(cfg, 3, 0, 3, j, "ULs")         # strides over set markers
        cfg = ex.conc(cfg, True, True, 2, 1, 0, "ULi")    # interior stop
    else:
        cfg = ex.cycL(cfg, 3, 0, 3, j - 1, "ULs")
        cfg = ex.conc(cfg, False, True, 3, None, 0, "ULsE")  # edge stride
        cfg = ex.conc(cfg, False, True, 2, None, 0, "ULo")   # stop at edge
    cfg = ex.cycR(cfg, 1, 1, 3 * j + 3, "UAr")        # A-return zeroing
    cfg = ex.conc(cfg, True, True, 6, 1, 2, "UEnd")   # rebuild anchor
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
