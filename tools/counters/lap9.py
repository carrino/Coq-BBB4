#!/usr/bin/env python3
"""Symbolic lap for #9 (1RB0LC_1RC0RD_1LA0LC_1RD0RA), double_counter,
edge D, gen comb (10), side R, kg=2^j-1, acc=3j.

Anchor D(j) = (10)^kg 1^acc, head on the rightmost 1, state D.
cconf: (D, rep [S1;S0] kg reversed... , 1, []) -- see D_conf below.

The doubling kg -> 2kg+1 is driven by a GRAY-CODE counter living in the
tail: at the i-th left-edge turnaround (state A, head at the new left
blank) the config is

  f_i = (A, [], 0, rep [1,0] (kg+1+i) ++ [1] ++ gray_region(G(kg-i), j))

with G(v) = v xor (v>>1) the reflected Gray code and

  gray_region(v, j) = [0] ++ concat_{k<j} [bit_k(v),0,0] ++ [1].

Consecutive f_i differ by ONE gray-bit flip (the doubling adds one comb
unit and decrements the Gray counter by one step).  This file is the
differential gate: it builds the f_i family symbolically and checks the
raw stepper walks f_i -> f_{i+1} exactly, plus the poke prefix
(D(j) -> f_0) and the final spread (f_kg -> D(j+1))."""
import sys
sys.path.insert(0, '.')
from executor import Exec, Wall, LAB

SPEC = "1RB0LC_1RC0RD_1LA0LC_1RD0RA"
A, B, C, D = 0, 1, 2, 3

def gray(v):
    return v ^ (v >> 1)

def bits(v, n):
    return [(v >> k) & 1 for k in range(n)]

def gray_region(v, j):
    out = [0]
    for b in bits(gray(v), j):
        out += [b, 0, 0]
    out += [1]
    return out

def D_conf(kg, acc):
    """(10)^kg 1^acc, head on rightmost 1, state D. As cconf (l,h,r)."""
    tape = [1, 0] * kg + [1] * acc
    # head on last cell (a 1); l = reverse(tape[:-1]); h=1; r=[]
    l = tape[:-1][::-1]
    return (D, l, 1, [])

def f_conf(i, kg, j):
    """i-th left-edge config: state A, head on new left blank."""
    cm = kg + 1 + i
    r = [1, 0] * cm + gray_region(kg - i, j)
    return (A, [], 0, r)

def raw_run(ex, cfg, stop_pred, budget):
    steps = 0
    q, l, h, r = cfg
    cur = (q, list(l), h, list(r))
    for _ in range(budget):
        if steps > 0 and stop_pred(cur):
            return steps, cur
        nxt = ex.cstep(cur)
        if nxt is None:
            return None
        cur = (nxt[0], list(nxt[1]), nxt[2], list(nxt[3]))
        steps += 1
    return None

def norm(cfg):
    q, l, h, r = cfg
    l, r = list(l), list(r)
    while l and l[-1] == 0: l.pop()
    while r and r[-1] == 0: r.pop()
    return (q, l, h, r)

def eqn(a, b):
    return norm(a) == norm(b)

def check(j, verbose=False):
    ex = Exec(SPEC)
    kg = (1 << j) - 1
    acc = 3 * j
    kg2, acc2 = 2 * kg + 1, acc + 3
    D0 = D_conf(kg, acc)
    D1 = D_conf(kg2, acc2)
    f = [f_conf(i, kg, j) for i in range(kg + 1)]
    budget = 200 * (kg + acc) ** 2 + 100000
    # poke prefix: D0 -> f_0 (first left-edge turn, state A head at new blank)
    def is_f0(c):
        return eqn(c, f[0])
    r0 = raw_run(ex, D0, is_f0, budget)
    if r0 is None:
        return f"j={j}: poke D0 -> f_0 FAILED"
    n_pre = r0[0]
    total = n_pre
    # mini-laps f_i -> f_{i+1}
    for i in range(kg):
        def is_next(c, fi=f[i + 1]):
            return eqn(c, fi)
        ri = raw_run(ex, f[i], is_next, budget)
        if ri is None:
            return f"j={j}: mini-lap f_{i} -> f_{i+1} FAILED"
        total += ri[0]
    # final spread: f_kg -> D1
    def is_D1(c):
        return eqn(c, D1)
    rf = raw_run(ex, f[kg], is_D1, budget)
    if rf is None:
        return f"j={j}: final f_kg -> D1 FAILED"
    total += rf[0]
    # cross-check against the plain raw lap count from D0 to D1
    def is_D1_from_D0(c):
        return c[0] == D and eqn(c, D1)
    rraw = raw_run(ex, D0, is_D1_from_D0, budget)
    n_raw = rraw[0] if rraw else -1
    ok = (total == n_raw)
    if verbose or not ok:
        print(f"j={j}: kg={kg} acc={acc}  pre={n_pre} total={total} raw={n_raw} "
              f"{'OK' if ok else 'MISMATCH'}")
    return None if ok else f"j={j}: step total {total} != raw {n_raw}"

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    # j range: keep k+acc modest so raw stays fast; hi caps the tape budget
    jmax = 2
    while (1 << (jmax + 1)) - 1 + 3 * (jmax + 1) <= hi:
        jmax += 1
    bad = 0
    for j in range(2, jmax + 1):
        e = check(j, verbose=True)
        if e:
            print("  ", e); bad += 1
    print(f"j=2..{jmax}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
