#!/usr/bin/env python3
"""Symbolic lap for #18 (1RB0RD_1LB0LC_1LD1LB_1RA1RD), interleave_counter,
edge A.  Anchor D(n) = E(n) (110)^(2n) 1, head one cell right of the
frontier (blank), state A; E(n) interleaves the low bits of n (LSB
nearest the comb) with 1s.  As a cconf the left list is

    l = 1 :: rep [0,1,1] (2n) ++ Ip(n),   h = 0,  r = []

with Ip(n) = rev(E(n)): Ip(1)=[1], Ip(2q)=[1,0]++Ip(q),
Ip(2q+1)=[1,1]++Ip(q).  One lap D(n) -> D(n+1) is two sweeps through
the mid shape M(n) = E(n+1) 010 (110)^(2n) 1; the increment (carry
over the [1,1] pairs, interior stop at a [1,0] pair / overflow off the
left tape edge) happens on sweep 1, sweep 2 rewrites 010 locally and
grows the comb."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0RD_1LB0LC_1LD1LB_1RA1RD"
A, B, C, D = 0, 1, 2, 3

def Ip(n):
    out = []
    while n > 1:
        out += [1, n & 1]
        n >>= 1
    return out + [1]

def carry(n):
    j = 0
    while (n >> j) & 1: j += 1
    return j, (n == (1 << j) - 1)

def D_conf(n):
    return (A, [1] + rep([0, 1, 1], 2 * n) + Ip(n), 0, [])

def lap(ex, n):
    ex.steps = 0
    j, ov = carry(n)
    z = 2 * n
    cfg = D_conf(n)

    # ---- sweep 1: the increment ----
    cfg = ex.conc(cfg, True, False, 3, 1, 0, "U1")      # (A,[1],0,[]) -> (C,[],1,[0,1])
    cfg = ex.cycL(cfg, 3, 0, 3, z, "U2")                # comb crossing
    if not ov:
        cfg = ex.cycL(cfg, 2, 0, 2, j, "U3")            # carry over [1,1] pairs
        cfg = ex.conc(cfg, True, True, 6, 3, 0, "U4i")  # interior stop
        cfg = ex.cycR(cfg, 2, 2, j + 1, "U5")           # recross pairs + comb [0,1]
    else:
        cfg = ex.cycL(cfg, 2, 0, 2, j - 1, "U3")
        cfg = ex.conc(cfg, False, True, 6, None, 0, "U4o")  # overflow stop, tape edge
        cfg = ex.cycR(cfg, 2, 2, j, "U5")
    cfg = ex.conc(cfg, True, True, 1, 0, 1, "UJ2")      # junction A->D
    cfg = ex.cycR(cfg, 3, 3, z - 1, "U10")              # comb recross
    cfg = ex.conc(cfg, True, False, 4, 0, 2, "U11")     # extension -> mid anchor

    # mid anchor check: M(n) = (A, 1 :: rep[0,1,1] z ++ [0,1,0] ++ Ip(n+1), 0, [])
    mid = (A, [1] + rep([0, 1, 1], z) + [0, 1, 0] + Ip(n + 1), 0, [])
    assert norm(cfg) == norm(mid), f"mid anchor mismatch:\n {norm(cfg)}\n {mid}"

    # ---- sweep 2: rewrite 010, grow comb ----
    cfg = ex.conc(cfg, True, False, 3, 1, 0, "U1")
    cfg = ex.cycL(cfg, 3, 0, 3, z, "U2")
    cfg = ex.conc(cfg, True, True, 8, 4, 0, "U9")       # 010-turnaround
    cfg = ex.cycR(cfg, 3, 3, z, "U10")
    cfg = ex.conc(cfg, True, False, 4, 0, 2, "U11")
    return ex.steps, cfg

def raw_lap(ex, n):
    cfg = D_conf(n)
    for it in range(1, 400 * n + 8000):
        cfg = ex.cstep(cfg)
        q, l, h, r = cfg
        if q == A and h == 0 and all(x == 0 for x in r):
            nc = norm(cfg)
            if nc == norm(D_conf(n + 1)):
                return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ex = Exec(SPEC)
    bad = 0
    for n in range(4, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, n)
        except (AssertionError, Wall) as e:
            print(f"n={n}: FAIL: {e}"); bad += 1
            if bad > 3: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(ex, n)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(D_conf(n + 1)))
        if not ok:
            print(f"n={n}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(D_conf(n+1)) else 'BAD'}")
            bad += 1
            if bad > 3: sys.exit(1)
    print(f"n=4..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
