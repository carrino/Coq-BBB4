#!/usr/bin/env python3
"""Symbolic MACRO lap for #33 (1RB1LD_1RC0RB_1LA1RB_0LD0LA), bounce_counter.

Macro anchor D(k) = 1^m 0^(2k), m = 2^k + 1, head on the last 0,
state B:  (B, l = 0^(2k-1) ++ 1^m, 0, []).

Same architecture as #8 (lap8.py) with the sweep roles at opposite
parity: the stable sweep-config keeps the counter word behind a 11
separator over a (10)-comb,

    Sc(a, w) = (A, [], 0, 0 :: rep([1,0], a) ++ [1,1] ++ Dw(w) ++ [1,1]),

the STABLE->MID sweep carries the digit increment (zeroing run over
the set pairs, 4-step flip, walk back over the zeros) and the
MID->STABLE sweep re-creates the separator two cells further out.
One macro lap = boot-in + (2^(k-1)-1) double-sweeps + terminal
double-sweep; each double-sweep is the same cell-uniform binary
increment Sc(a, 1^j 0 X) -> Sc(a+1, 0^j 1 X) as #8."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, rep, norm, LAB

SPEC = "1RB1LD_1RC0RB_1LA1RB_0LD0LA"
A, B, C, D = 0, 1, 2, 3

def Dw(w):
    out = []
    for b in w:
        out += [b, b]
    return out

def Sc(a, w):
    return (A, [], 0, [0] + rep([1, 0], a) + [1, 1] + Dw(w) + [1, 1])

def Dk(k):
    m = (1 << k) + 1
    return (B, [0] * (2 * k - 1) + [1] * m, 0, [])

def sweepA(ex, cfg, a, j):
    """stable -> mid: the digit increment (j = trailing set digits)."""
    cfg = ex.conc(cfg, True, True, 3, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 2, a - 1, "UC")        # collapse
    cfg = ex.conc(cfg, True, True, 2, 0, 2, "UJ2")   # enter the separator
    cfg = ex.cycR(cfg, 1, 1, 2 * j, "UBr")       # zeroing run over set pairs
    cfg = ex.conc(cfg, True, True, 4, 0, 2, "UT2")   # flip the stop digit
    cfg = ex.cycL(cfg, 1, 0, 1, 2 * j, "UD0")    # walk back over the zeros
    cfg = ex.conc(cfg, True, True, 2, 2, 0, "UJ3")   # land on the solid block
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "UJ")    # junction into the spread
    cfg = ex.cycL(cfg, 2, 0, 2, a, "USp")        # spread
    cfg = ex.conc(cfg, False, True, 1, None, 0, "UE")
    return cfg

def sweepB(ex, cfg, a):
    """mid -> stable: re-create the separator (uniform in the word)."""
    cfg = ex.conc(cfg, True, True, 3, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 2, a, "UC")
    cfg = ex.conc(cfg, True, True, 3, 1, 1, "UT1")
    cfg = ex.cycL(cfg, 2, 0, 2, a + 1, "USp")
    cfg = ex.conc(cfg, False, True, 1, None, 0, "UE")
    return cfg

def sweepA_term(ex, cfg, a, o):
    """stable all-ones -> D(k+1): the settle (no clear digit to stop at)."""
    cfg = ex.conc(cfg, True, True, 3, 0, 3, "U1")
    cfg = ex.cycR(cfg, 2, 2, a - 1, "UC")
    cfg = ex.conc(cfg, True, True, 2, 0, 2, "UJ2")
    cfg = ex.cycR(cfg, 1, 1, o, "UBr")
    cfg = ex.conc(cfg, True, False, 1, 0, None, "UTD")
    return cfg

def macro_lap(ex, k):
    ex.steps = 0
    m = (1 << k) + 1
    cfg = Dk(k)
    # boot-in half sweep
    cfg = ex.conc(cfg, True, False, 3, 1, 0, "UT0")
    cfg = ex.cycL(cfg, 1, 0, 1, 2 * k - 2, "UD0")
    cfg = ex.conc(cfg, True, True, 1, 1, 0, "UJ0")
    cfg = ex.cycL(cfg, 2, 0, 2, (1 << (k - 1)), "USp")
    cfg = ex.conc(cfg, False, True, 1, None, 0, "UE")
    a = (1 << (k - 1)) - 1
    w = [0] * (k - 1)
    # the boot-in exit is the PRE-STABLE mid; one mid->stable sweep first
    cfg = sweepB(ex, cfg, a)
    assert norm(cfg) == norm(Sc(a + 1, w)), f"boot-in: {norm(cfg)}"
    a += 1
    # the double-sweeps
    while 0 in w:
        j = 0
        while w[j] == 1:
            j += 1
        cfg = sweepA(ex, cfg, a, j)
        cfg = sweepB(ex, cfg, a)
        w = [0] * j + [1] + w[j + 1:]
        a += 1
        assert norm(cfg) == norm(Sc(a, w)), f"dlap a={a} w={w}"
    # terminal settle sweep
    cfg = sweepA_term(ex, cfg, a, 2 * (k - 1) + 2)
    assert norm(cfg) == norm(Dk(k + 1)), f"terminal: {norm(cfg)}"
    return ex.steps, cfg

def raw_lap(ex, k):
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
