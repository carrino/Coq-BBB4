import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lg3
def cent(p, d): return d + 3 if p == 0 else d - 1
def uncent(p, c): return c - 3 if p == 0 else c + 1
fwd = {}
for s in (-1, 0):
    for p in (0, 1):
        for c in (-1, 0, 1):
            if s + c in (-1, 0):
                fwd[((s, p), uncent(p, c))] = (s + c, 1 - p)
ENDS = {(-1, 0): [(3, 1)], (-1, 1): [(4, 1), (5, 2)], (0, 0): [(2, 1)], (0, 1): [(3, 1), (4, 2)]}
end = {q: [(b1 - 2 * bk, bk) for b1, bk in lst] for q, lst in ENDS.items()}
lang = lg3.Lang(2, (1,), (0,), fwd, end, (0, 0), shift=1)
# the left tails: b_0 (shifted), then only centred digit 0 (every element
# the sweep passed has pass parity)
lfwd = {}
for (q, d), q2 in fwd.items():
    s, p = q
    if q == (0, 0) or cent(p, d) == 0:
        lfwd[(q, d)] = q2
lang2 = lg3.Lang(2, (1,), (0,), fwd, end, (0, 0), shift=1, lfwd=lfwd)
lfwd3 = {(q, d): q2 for (q, d), q2 in fwd.items() if cent(q[1], d) == 0}
lstart3 = [(d, q2) for (q, d), q2 in fwd.items() if q == (0, 0)]
lang3 = lg3.Lang(2, (1,), (0,), fwd, end, (0, 0), shift=1, lfwd=lfwd3, lstart=lstart3)
