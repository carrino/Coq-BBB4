#!/usr/bin/env python3
"""Full symbolic validation of the inner-counter overflow decomposition for
1RB1LA_0LA1RC_0LD0RB_0LA1RD.

Outer anchor : Cc p  = (A, Ip p ++ [1,0], 0, [0])
Inner anchor : Cin v = (A, Ip v ++ [1],   0, [1,0])

interior lap : P1(2) RIP^{2j+1} STPI(1) TRN(1) RET^j FIN(3)      [exact]
inner lap    : P1i(6) RIP^{2j+1} STPI(1) TRN(1) RET^j FINi(7)    [exact]
boot         : P1(2) RIP^{2j'+2} STPO(2) RET^{j'+1} FINx(5)      [-> Cin(2^j')]
exit         : P1i(6) RIP^{2K} STPO'(?) RET^{K} FIN(3)           [-> Cc(2^K) lift]
"""
import sys
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
from executor import Exec, Wall
from emit_interleave import ENC, LAB, Raw

spec = '1RB1LA_0LA1RC_0LD0RB_0LA1RD'
Ip = ENC['Ip']
ex = Exec(spec)
raw = Raw(spec)
A = 0

def win(bl, br, q, l, h, r, n):
    return ex.wsteps(bl, br, q, list(l), h, list(r), n)

def cyc_l1(cfg, k):   # 1-cell leftward A-run
    q, l, h, r = cfg
    assert l[:k] == [1]*k and h == 1 and q == A
    return (A, l[k:], 1, [1]*k + r)

def cyc_r2(cfg, k):   # 2-cell BC rewrite
    q, l, h, r = cfg
    assert q == 1 and h == 1 and r[:2*k] == [1]*(2*k)
    return (1, [0,1]*k + l, 1, r[2*k:])

def conc(cfg, bl, br, n, lw, rw, expect=None):
    q, l, h, r = cfg
    lw = len(l) if lw is None else lw
    rw = len(r) if rw is None else rw
    out = win(bl, br, q, l[:lw], h, r[:rw], n)
    res = (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:])
    if expect is not None:
        assert (out[0], tuple(out[1]), out[2], tuple(out[3])) == expect, \
            ('window mismatch', (out[0], out[1], out[2], out[3]), expect)
    return res

def j_of(v):
    j = 0
    while (v >> j) & 1:
        j += 1
    return j

def sym_interior(p):
    j = j_of(p)
    cfg = (A, Ip(p) + [1, 0], 0, [0])
    cfg = conc(cfg, True, True, 2, 0, 1, (A, (), 1, (0,)))        # P1
    cfg = cyc_l1(cfg, 2*j + 1)                                     # RIP
    cfg = conc(cfg, True, True, 1, 1, 0, (A, (), 0, (1,)))         # STPI
    cfg = conc(cfg, True, True, 1, 0, 1, (1, (1,), 1, ()))         # TRN
    cfg = cyc_r2(cfg, j)                                           # RET
    cfg = conc(cfg, True, True, 3, 0, None)                        # FIN
    n = 2 + (2*j+1) + 1 + 1 + 2*j + 3
    return cfg, n

def sym_inner(v):
    j = j_of(v)
    cfg = (A, Ip(v) + [1], 0, [1, 0])
    cfg = conc(cfg, True, True, 6, 0, 2, (A, (), 1, (1, 0)))       # P1i
    cfg = cyc_l1(cfg, 2*j + 1)                                     # RIP
    cfg = conc(cfg, True, True, 1, 1, 0, (A, (), 0, (1,)))         # STPI
    cfg = conc(cfg, True, True, 1, 0, 1, (1, (1,), 1, ()))         # TRN
    cfg = cyc_r2(cfg, j)                                           # RET
    cfg = conc(cfg, True, True, 7, 0, None)                        # FINi
    n = 6 + (2*j+1) + 1 + 1 + 2*j + 7
    return cfg, n

def sym_boot(jp):     # from Cc(2^{jp+1}-1); lands Cin(2^jp)
    p = (1 << (jp + 1)) - 1
    cfg = (A, Ip(p) + [1, 0], 0, [0])
    cfg = conc(cfg, True, True, 2, 0, 1, (A, (), 1, (0,)))         # P1
    cfg = cyc_l1(cfg, 2*jp + 2)                                    # RIP (+wall)
    cfg = conc(cfg, False, True, 2, None, 0)                       # STPO
    cfg = cyc_r2(cfg, jp + 1)                                      # RET
    cfg = conc(cfg, True, False, 5, 1, None)                       # FINx
    n = 2 + (2*jp+2) + 2 + 2*(jp+1) + 5
    return cfg, n

def sym_exit(K):      # from Cin(2^K-1); lands Cc(2^K) one-left-blank short
    u = (1 << K) - 1
    cfg = (A, Ip(u) + [1], 0, [1, 0])
    cfg = conc(cfg, True, True, 6, 0, 2, (A, (), 1, (1, 0)))       # P1i
    cfg = cyc_l1(cfg, 2*K)                                         # RIP (+wall)
    cfg = conc(cfg, False, True, 2, None, 0)                       # STPO'
    cfg = cyc_r2(cfg, K)                                           # RET
    cfg = conc(cfg, True, True, 3, 0, 2)                           # FIN
    n = 6 + 2*K + 2 + 2*K + 3
    return cfg, n

def raw_lap(p, tgt, maxs=100000):
    cfg = (A, Ip(p) + [1, 0], 0, [0])
    for t in range(1, maxs):
        cfg = raw.step(cfg)
        if cfg == tgt:
            return t
    return None

ok = 0
for p in range(2, 200):
    j = j_of(p)
    if p == (1 << j) - 1:
        continue
    cfg, n = sym_interior(p)
    tgt = (A, Ip(p+1) + [1, 0], 0, [0])
    assert cfg == tgt, (p, cfg)
    assert raw_lap(p, tgt) == n, p
    ok += 1
print('interior laps exact + step-exact: %d checked' % ok)

ok = 0
for v in range(2, 300):
    j = j_of(v)
    if v == (1 << j) - 1:
        continue
    cfg, n = sym_inner(v)
    assert cfg == (A, Ip(v+1) + [1], 0, [1, 0]), (v, cfg)
    ok += 1
print('inner laps exact: %d checked' % ok)

for jp in range(0, 8):
    cfg, n = sym_boot(jp)
    assert cfg == (A, Ip(1 << jp) + [1], 0, [1, 0]), (jp, cfg)
print('boot exact for jp=0..7')

for K in range(1, 9):
    cfg, n = sym_exit(K)
    assert cfg == (A, Ip(1 << K) + [1], 0, [0]), (K, cfg)
print('exit exact (left one blank short of tail [1,0]) for K=1..8')

# full outer overflow differential: boot + inner laps + exit == raw
for K in range(2, 8):
    p = (1 << K) - 1
    n = sym_boot(K - 1)[1]
    for v in range(1 << (K - 1), (1 << K) - 1):
        n += sym_inner(v)[1]
    n += sym_exit(K)[1]
    tgt = (A, Ip(p + 1) + [1], 0, [0])
    r = raw_lap(p, tgt)
    assert r == n, (K, r, n)
print('OUTER OVERFLOW composition == raw trace, step-exact, K=2..7')

# dump the five window lemmas needed beyond the interior chain
print()
print('U_P1i :', win(True, True, A, [], 0, [1, 0], 6))
print('U_FINi:', win(True, True, 1, [], 1, [1, 1, 0], 7))
print('U_STPO:', win(False, True, A, [0], 1, [], 2))
print('U_FINx:', win(True, False, 1, [0], 1, [0], 5))
print('U_FIN :', win(True, True, 1, [], 1, [1, 0], 3))
print('U_P1  :', win(True, True, A, [], 0, [0], 2))
print('exit STPO (true blank deep end):', win(False, True, A, [], 1, [], 2))
