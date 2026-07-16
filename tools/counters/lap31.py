#!/usr/bin/env python3
"""Full symbolic lap for #31 (1RB1LD_1RC0RB_0LA1RB_0LD1LA)."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, bits, W, carry, rep, norm, LAB

SPEC = "1RB1LD_1RC0RB_0LA1RB_0LD1LA"
A, B, C, D = 0, 1, 2, 3

def C_conf(a):
    t = [1, 1, 0] * a + W(a)
    return (B, [1], 1, t[2:])

def lap(ex, a):
    ex.steps = 0
    j, ov = carry(a)
    Wa = W(a)
    cfg = C_conf(a)
    assert cfg[3] == rep([0, 1, 1], a - 1) + [0] + Wa

    # S1
    cfg = ex.cycR(cfg, 3, 3, a - 1, "U2")
    cfg = ex.conc(cfg, True, True, 4, 0, 2, "U3")          # (B,1,[0,0])->(D,0,[1,0])
    cfg = ex.cycL(cfg, 3, 0, 3, a - 1, "U4")
    cfg = ex.conc(cfg, False, True, 3, None, 0, "U5")      # (D,[1],0)->(B,[1],1,[0])
    assert cfg[:3] == (B, [1], 1)

    # S2 up + increment
    cfg = ex.cycR(cfg, 3, 3, a - 1, "U2")
    if j == 0:
        cfg = ex.conc(cfg, True, True, 8, 0, 4, "U6z")     # (B,1,[0,1,0,0])->(D,0,[1,1,1,0])
    else:
        cfg = ex.conc(cfg, True, True, 4, 0, 4, "U6a")     # (B,1,[0,1,0,1])->(C,1,[]) l+=[1,1,1,0]
        cfg = ex.cycR(cfg, 2, 2, j - 1, "U7")              # (C,1,[0,1])->(C,1,[]) l+=[1,1]
        if not ov:
            cfg = ex.conc(cfg, True, True, 3, 0, 2, "U8")  # (C,1,[0,0])->(A,1,[0]) l+=[1]
        else:
            cfg = ex.conc(cfg, True, False, 3, 0, None, "U8v")
        cfg = ex.cycL(cfg, 2, 0, 2, j + 1, "U9")           # ones walk
        cfg = ex.conc(cfg, True, True, 1, 1, 0, "U9g")     # glue (A,[0],1)->(D,0,[1])
    assert cfg[0] == D and cfg[2] == 0
    cfg = ex.cycL(cfg, 3, 0, 3, a - 1, "U4")
    cfg = ex.conc(cfg, False, True, 3, None, 0, "U5")

    # S3
    cfg = ex.cycR(cfg, 3, 3, a - 1, "U2")
    cfg = ex.cycR(cfg, 3, 3, 1, "U2")                      # one more unit over [0,1,1]
    cfg = ex.cycR(cfg, 1, 1, 2 * j + 1, "U10")             # zap (B,1,[1])->(B,1) l+=[0]
    if not ov:
        cfg = ex.conc(cfg, True, True, 4, 0, 2, "U3")      # same unit as S1 turn
    else:
        cfg = ex.conc(cfg, True, False, 4, 0, None, "U3v")
    cfg = ex.cycL(cfg, 1, 0, 1, 2 * j + 1, "U11")          # zero walk (D,[0],0)->(D,0,[0])
    cfg = ex.cycL(cfg, 3, 0, 3, a, "U4")                   # S3 down, one extra unit
    cfg = ex.conc(cfg, False, True, 3, None, 0, "U5")      # event closer
    return ex.steps, cfg

def raw_lap(ex, a):
    cfg = C_conf(a)
    for n in range(1, 8000 * a + 40000):
        cfg = ex.cstep(cfg)
        q, l, h, r = cfg
        ln = list(l)
        while ln and ln[-1] == 0: ln.pop()
        if q == B and h == 1 and ln == [1]:
            tape = [1, 1] + list(r)
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
        got = raw_lap(ex, a)
        n_raw, cfg_raw = got
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
