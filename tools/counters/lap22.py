#!/usr/bin/env python3
"""Symbolic lap for #22 (1RB1LA_1LC0RB_0LA0LD_1RA0RB), spacer_counter,
edge B, voff -1, zoff 2.  Anchor S(m) = B(m) 11 0^(2m+4) 1(head), state B.
cconf: (C, rep [0] (2m+2) ++ [1,1] ++ bitsLSB(m), 1, [])."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB1LA_1LC0RB_0LA0LD_1RA0RB"
A, B, C, D = 0, 1, 2, 3

def bitsL(m):
    out = []
    while m: out.append(m & 1); m >>= 1
    return out

def carry(m):
    j = 0
    while (m >> j) & 1: j += 1
    return j, (m == (1 << j) - 1)

def S_conf(m):
    return (B, [0] * (2 * m + 4) + [1, 1] + bitsL(m), 1, [])

def lap(ex, m):
    ex.steps = 0
    j, ov = carry(m)
    z = 2 * m + 4
    cfg = S_conf(m)

    # prologue: 8 steps, eats 2 spacer zeros, deposits frontier 11 + r=[1]
    cfg = ex.conc(cfg, True, False, 8, 2, 0, "U1")
    # second block: 9 steps
    cfg = ex.conc(cfg, True, False, 9, 3, 1, "U2")
    # transcription: cycLW(lw=[1], u=[0], rw=[], w=[1]) x (z-2)
    q, l, h, r = cfg
    assert l[:1] == [1] and l[1:z-1] == [0]*(z-2), "transcription l shape"
    # apply manually (cycLW): unit (D,([1,0],0,[])) -> (D,([1],0,[1]))
    out = ex.wsteps(True, True, C, [1, 0], 0, [], 5)
    assert out == (C, [1], 0, [1]), f"U3 unit: {out}"
    ex.record("U3", True, True, 5, (C, (1, 0), 0, ()), (C, (1,), 0, (1,)))
    assert cfg[0] == C and cfg[2] == 0
    ex.steps += 5 * (z - 2)
    cfg = (C, [1] + l[z-1:], 0, [1] * (z - 2) + r)
    # glue: (D,([1],0,[])) -> (B,([],1,[0]))
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "U4")
    # carry: l = [1,1] ++ bits(m); ones run
    if not ov:
        # cycL(u=[1],rw=[],w=[1],P=1) x (j+2), then 1 step onto the 0-bit
        cfg = ex.cycL(cfg, 1, 0, 1, j + 2, "U5")
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U6")   # (B,([0],1,[]))->(B,([],0,[1]))
        cfg = ex.conc(cfg, True, True, 1, 0, 1, "U7")   # (B,([],0,[1]))->(C,([1],1,[]))
    else:
        cfg = ex.cycL(cfg, 1, 0, 1, j + 1, "U5")
        # (B,([1],1,[1])) -> (C,([1],1,[1,1])), left edge
        cfg = ex.conc(cfg, False, True, 3, None, 1, "U8")
    # C1 return-run over the shuttle ones: cycR(u=[1],w=[0],P=1) x (j+2)
    cfg = ex.cycR(cfg, 1, 1, j + 2, "U9")
    # land on the glue zero: (C,([],1,[0])) -> (C,([0],0,[]))
    cfg = ex.conc(cfg, True, True, 1, 0, 1, "U9b")
    # mini-block: (C,([0,0,0],0,[])) -> (C,([1,1],1,[1]))
    cfg = ex.conc(cfg, True, True, 7, 3, 0, "U10")
    # final return sweep: consume all remaining ones
    q, l, h, r = cfg
    ones = 0
    while ones < len(r) and r[ones] == 1: ones += 1
    cfg = ex.cycR(cfg, 1, 1, ones, "U9")
    assert cfg[3] == [] or all(x == 0 for x in cfg[3]), f"return r: {cfg[3][:8]}"
    return ex.steps, cfg

def raw_lap(ex, m):
    cfg = S_conf(m)
    for n in range(1, 3000 * m + 40000):
        cfg = ex.cstep(cfg)
        q, l, h, r = cfg
        if q == B and h == 1 and all(x == 0 for x in r):
            m2 = m + 1; z2 = 2 * m2 + 4
            ln = list(l)
            if (len(ln) >= z2 + 2 and ln[:z2] == [0]*z2
                    and ln[z2:z2+2] == [1, 1]
                    and [x for x in ln[z2+2:] if 1] is not None):
                bl = ln[z2+2:]
                while bl and bl[-1] == 0: bl.pop()
                if bl == bitsL(m2):
                    return n, cfg
    return None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ex = Exec(SPEC)
    bad = 0
    for m in range(2, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, m)
        except (AssertionError, Wall) as e:
            print(f"m={m}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, m)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(S_conf(m + 1)))
        if not ok:
            print(f"m={m}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(S_conf(m+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"m=2..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
