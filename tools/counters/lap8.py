#!/usr/bin/env python3
"""Symbolic MACRO lap for #8 (1RB0LC_1LC0RB_1RD1LA_0LA1RB), bounce_counter.

Macro anchor D(k) = 1^m 0^(2k+1), m = 2^k-1, head on the last 0,
state B:  (B, l = 0^(2k) ++ 1^m, 0, []).

One macro lap D(k) -> D(k+1) chains:
  - a boot-in half sweep to the first stable sweep-config;
  - 2^(k-1)-1 double-sweeps, each a CELL-UNIFORM binary increment
      Sc(a, 1^j 0 X) -> Sc(a+1, 0^j 1 X)
    on the working-area digit word (00/11 pairs after a 00 separator,
    trailing accumulator 1^2 fixed in this view) -- NO interior/
    overflow case split exists at the cell level, the accumulator
    merge is pure decode;
  - a terminal double-sweep from the all-ones word settling to D(k+1).

Stable sweep-config: Sc(a, w) = (A, [], 0, 1 :: (01)^a ++ 00 ++ Dw(w)
++ 11), comb index a (concrete comb (01)^(a+1) counting the head).
The measure driving the Coq well-founded composition (MeasureGlue) is
cval(w) = value of the pointwise complement of w, LSB first: each
double-sweep decrements it by exactly 1."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB0LC_1LC0RB_1RD1LA_0LA1RB"
A, B, C, D = 0, 1, 2, 3

def Dw(w):
    out = []
    for b in w:
        out += [b, b]
    return out

def Sc(a, w):
    return (A, [], 0, [1] + rep([0, 1], a) + [0, 0] + Dw(w) + [1, 1])

def Dk(k):
    m = (1 << k) - 1
    return (B, [0] * (2 * k) + [1] * m, 0, [])

def sweepA(ex, cfg, a):
    cfg = ex.conc(cfg, True, True, 5, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 4, a - 1, "UC")     # collapse
    cfg = ex.conc(cfg, True, True, 6, 0, 2, "UT1")
    cfg = ex.cycL(cfg, 2, 0, 2, a, "USp")     # spread
    cfg = ex.conc(cfg, False, True, 2, None, 0, "UE")
    return cfg

def sweepB(ex, cfg, a, o):
    cfg = ex.conc(cfg, True, True, 5, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 4, a, "UC")
    cfg = ex.cycR(cfg, 1, 1, o, "UBr")        # zeroing run
    cfg = ex.conc(cfg, True, True, 6, 0, 2, "UT1")
    cfg = ex.cycL(cfg, 1, 0, 3, o, "UZ")      # walk back over the zeros
    cfg = ex.cycL(cfg, 2, 0, 2, a + 1, "USp")
    cfg = ex.conc(cfg, False, True, 2, None, 0, "UE")
    return cfg

def sweepB_term(ex, cfg, a, o):
    cfg = ex.conc(cfg, True, True, 5, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 4, a, "UC")
    cfg = ex.cycR(cfg, 1, 1, o, "UBr")
    cfg = ex.conc(cfg, True, False, 1, 0, None, "UTD")
    return cfg

def macro_lap(ex, k):
    ex.steps = 0
    m = (1 << k) - 1
    cfg = Dk(k)
    # boot-in half sweep
    cfg = ex.conc(cfg, True, False, 5, 1, 0, "UT0")
    cfg = ex.cycL(cfg, 1, 0, 3, 2 * k - 1, "UZ")
    cfg = ex.cycL(cfg, 2, 0, 2, (1 << (k - 1)) - 1, "USp")
    cfg = ex.conc(cfg, False, True, 2, None, 0, "UE")
    a = (1 << (k - 1)) - 1
    w = [0] * (k - 1)
    assert norm(cfg) == norm(Sc(a, w)), f"boot-in: {norm(cfg)} vs {norm(Sc(a,w))}"
    # the double-sweeps
    while 0 in w:
        j = 0
        while w[j] == 1:
            j += 1
        cfg = sweepA(ex, cfg, a)
        cfg = sweepB(ex, cfg, a, 2 * j + 1)
        w = [0] * j + [1] + w[j + 1:]
        a += 1
        assert norm(cfg) == norm(Sc(a, w)), f"dlap a={a} w={w}"
    # terminal double-sweep
    cfg = sweepA(ex, cfg, a)
    cfg = sweepB_term(ex, cfg, a, 2 * (k - 1) + 3)
    assert norm(cfg) == norm(Dk(k + 1)), f"terminal: {norm(cfg)}"
    return ex.steps, cfg

def raw_lap(ex, k):
    m = (1 << k) - 1
    cfg = Dk(k)
    tgt = norm(Dk(k + 1))
    for it in range(1, 40 * (1 << k) * (1 << k) + 100000):
        cfg = ex.cstep(cfg)
        if cfg[0] == B and norm(cfg) == tgt:
            return it, cfg
    return None, None

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    ex = Exec(SPEC)
    bad = 0
    total_dlaps = 0
    for k in range(2, hi + 1):
        try:
            n_sym, cfg_sym = macro_lap(ex, k)
        except (AssertionError, Wall) as e:
            print(f"k={k}: FAIL: {e}"); bad += 1
            continue
        total_dlaps += (1 << (k - 1))
        n_raw, cfg_raw = raw_lap(ex, k)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw))
        if not ok:
            print(f"k={k}: sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'}")
            bad += 1
    print(f"k=2..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'} "
          f"({total_dlaps} double-sweeps validated)")
    print("units:")
    ex.dump_units()
