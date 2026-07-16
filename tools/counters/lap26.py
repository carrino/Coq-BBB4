#!/usr/bin/env python3
"""Symbolic lap for #26 (1RB1LC_0LC0RB_1RD1LA_1RB0LA), mono_counter,
edge A, hoff -1.  Skeleton = #10's with a 1-step prologue and 6-step
event closer.  Differential validation + unit dump."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, bits, W, carry, rep, norm, LAB

SPEC = "1RB1LC_0LC0RB_1RD1LA_1RB0LA"
A, B, C, D = 0, 1, 2, 3

def C_conf(a):
    # head one LEFT of the comb: (A, [], 0, comb^a ++ W)
    t = [1, 1, 0] * a + W(a)
    return (A, [], 0, t)

def lap(ex, a):
    ex.steps = 0
    j, ov = carry(a)
    Wa = W(a)
    cfg = C_conf(a)
    # r = [1] ++ rep(LU,a-1) ++ [1,0] ++ W   (LU = [1,0,1])
    assert cfg[3] == [1] + rep([1, 0, 1], a - 1) + [1, 0] + Wa
    # prologue: 1 step onto the comb
    cfg = ex.conc(cfg, False, True, 1, None, 1, "U1")     # window: r[0]
    assert cfg[0] == B and cfg[1] == [1] and cfg[2] == 1
    # S1 up
    cfg = ex.cycR(cfg, 3, 5, a - 1, "U2")
    cfg = ex.conc(cfg, True, True, 6, 0, 3, "U3")
    assert cfg[0] == C and cfg[2] == 1, f"{LAB[cfg[0]]},{cfg[2]}"
    cfg = ex.cycL(cfg, 3, 0, 5, a - 1, "U4")
    assert cfg[1] == [1, 0, 1]
    cfg = ex.conc(cfg, False, True, 7, None, 0, "U5")
    assert cfg[0] == B and cfg[1] == [1] and cfg[2] == 1
    # S2 up + increment
    cfg = ex.cycR(cfg, 3, 5, a, "U2")
    if not ov:
        cfg = ex.cycR(cfg, 2, 4, j, "U6")
        cfg = ex.conc(cfg, True, True, 5, 0, 3, "U7")
        cfg = ex.cycL(cfg, 2, 0, 2, j + 1, "U8")
    else:
        cfg = ex.cycR(cfg, 2, 4, j, "U6")
        cfg = ex.conc(cfg, True, False, 5, 0, None, "U9")
        cfg = ex.cycL(cfg, 2, 0, 2, j + 1, "U8")
    assert cfg[1] == rep([1, 0, 1], a - 1) + [1, 0, 1], "post-inc l"
    cfg = ex.cycL(cfg, 3, 0, 5, a - 1, "U4")
    cfg = ex.conc(cfg, False, True, 7, None, 0, "U5")
    # S3
    cfg = ex.cycR(cfg, 3, 5, a, "U2")
    cfg = ex.cycR(cfg, 2, 2, j + 1, "U10")
    if not ov:
        cfg = ex.conc(cfg, True, True, 7, 1, 2, "U11")
    else:
        cfg = ex.conc(cfg, True, False, 7, 1, None, "U14")
    cfg = ex.cycL(cfg, 1, 1, 3, 2 * j + 1, "U12")
    cfg = ex.conc(cfg, True, True, 3, 1, 1, "U13")
    assert cfg[1] == rep([1, 0, 1], a - 1) + [1, 0, 1], "post-k l"
    cfg = ex.cycL(cfg, 3, 0, 5, a - 1, "U4")
    # event closer: 6 steps to the next anchor (head 1 left of comb)
    cfg = ex.conc(cfg, False, True, 6, None, 0, "U15")
    return ex.steps, cfg

def raw_lap(ex, a):
    cfg = C_conf(a)
    lo = 0
    for n in range(1, 8000 * a + 40000):
        cfg = ex.cstep(cfg)
        q, l, h, r = cfg
        if q == A and h == 0 and all(x == 0 for x in l):
            tape = list(r)
            aa = 0
            while tape[3*aa:3*aa+3] == [1, 1, 0]: aa += 1
            if aa > a:
                wc = tape[3*aa:]
                while wc and wc[-1] == 0: wc.pop()
                val = 0; ok = len(wc) > 0
                for i, cc in enumerate(wc):
                    if i % 2 == 0:
                        if cc: ok = False; break
                    elif cc: val |= 1 << (i // 2)
                if ok and val == aa:
                    return n, cfg
    return None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    ex = Exec(SPEC)
    bad = 0
    for a in range(2, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, a)
        except (AssertionError, Wall) as e:
            print(f"a={a}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, a)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(C_conf(a + 1)))
        if not ok:
            print(f"a={a}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(C_conf(a+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"a=2..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
