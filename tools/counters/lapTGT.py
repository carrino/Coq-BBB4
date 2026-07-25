#!/usr/bin/env python3
"""Symbolic comb-free lap for target 0RB---_0LC1RB_1LA1LD_1LC0RB
(interleave-counter, complemented encoding Jp, edge B).

Anchor  Cf(m) = (B, Jp(m) ++ [0], 0, [])   -- head at the fixed right
(LSB) frontier (blank), counter Jp(m) on the LEFT list nearest-first,
NO comb.  Jp = Ip with the data cell swapped:
    Jp(xH)=[1]; Jp(xO q)=1::1::Jp q; Jp(xI q)=1::0::Jp q.
The monotone index m increments (binary); the decoded interleave value
descends within each doubling block, so the raw carry runs in the
complement sense -- hence Jp, not Ip.

One lap Cf(m) -> Cf(m+1) is a SINGLE sweep:
  prologue (read frontier, turn left) ; leftward carry ripple over the
  low set-bit pairs (cview j) ; interior stop (flip clear pair) OR
  overflow stop off the DEEP-LEFT edge (fresh MSB pair, state A fires) ;
  rightward return to the frontier.  No comb, no junction, no 2nd sweep.
"""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "0RB---_0LC1RB_1LA1LD_1LC0RB"
A, B, C, D = 0, 1, 2, 3

def Jp(m):
    out = []
    while m > 1:
        out += [1, 1 - (m & 1)]   # xO(low0)->[1,1], xI(low1)->[1,0]
        m >>= 1
    return out + [1]

def carry(m):
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)   # (#low set bits, overflow?)

def Cf(m):
    return (B, Jp(m) + [0], 0, [])

def lap(ex, m):
    ex.steps = 0
    j, ov = carry(m)                 # j = #low set bits ; ov = all-ones (overflow)
    cfg = Cf(m)
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "P1")          # prologue: read frontier, turn L
    if not ov:
        cfg = ex.cycL(cfg, 2, 0, 2, j, "RIP")             # carry ripple over set pairs
        cfg = ex.conc(cfg, True, True, 2, 2, 0, "STPI")   # interior stop (flip clear pair)
        cfg = ex.cycR(cfg, 1, 1, 2 * j, "RET")            # return over deposited ones
        cfg = ex.conc(cfg, True, True, 1, 0, 1, "FIN")    # close at frontier
    else:
        cfg = ex.cycL(cfg, 2, 0, 2, j - 1, "RIP")         # ripple over all but last set pair
        cfg = ex.conc(cfg, False, True, 4, None, 0, "STPO")  # overflow stop off DEEP-LEFT edge
        cfg = ex.cycR(cfg, 1, 1, 2 * j, "RET")
        cfg = ex.conc(cfg, True, True, 1, 0, 1, "FIN")
    return ex.steps, cfg

def raw_lap(ex, m):
    cfg = Cf(m)
    for it in range(1, 400 * (m.bit_length() + 2) + 200):
        cfg = ex.cstep(cfg)
        q, l, h, r = cfg
        if q == B and h == 0 and all(x == 0 for x in r):
            if norm(cfg) == norm(Cf(m + 1)):
                return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    ex = Exec(SPEC)
    bad = 0
    for m in range(1, hi + 1):
        try:
            n_sym, cfg_sym = lap(ex, m)
        except (AssertionError, Wall) as e:
            print(f"m={m}: FAIL: {e}"); bad += 1
            if bad > 6: break
            continue
        n_raw, cfg_raw = raw_lap(ex, m)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(Cf(m + 1)))
        if not ok:
            print(f"m={m}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"next={'OK' if norm(cfg_sym)==norm(Cf(m+1)) else 'BAD'}")
            bad += 1
            if bad > 6: break
    print(f"m=1..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
    print("units:")
    ex.dump_units()
