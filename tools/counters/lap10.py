#!/usr/bin/env python3
"""Final symbolic lap for #10, unified phases; mirrors the Coq proof 1:1.

Unit lemmas (wsteps = walled steps; lw/rw = blank-materializing when False):
  U1  prologue  wsteps F T 2 (C,([],1,[]))      = (B,([1],1,[]))
  U2  R-cross   wsteps T T 5 (B,([],1,[1,0,1])) = (B,([1,1,0],1,[]))
  U3  S-turn    wsteps T T 6 (B,([],1,[1,0,0])) = (C,([1,0],1,[0]))
  U4  L-cross   wsteps T T 5 (C,([1,0,1],1,[])) = (C,([],1,[1,0,1]))
  U5  edge      wsteps F T 7 (C,([1,0,1],1,[])) = (B,([1],1,[1,0,1]))
  U6  carry     wsteps T T 4 (B,([],1,[0,1]))   = (B,([1,1],1,[]))
  U7  stop      wsteps T T 5 (B,([],1,[0,0,0])) = (C,([1],1,[0,0]))
  U8  ones-walk wsteps T T 2 (C,([1,1],1,[]))   = (C,([],1,[1,1]))
  U9  stop-ov   wsteps T F 5 (B,([],1,[]))      = (C,([1],1,[0]))
  U10 k-cross   wsteps T T 2 (B,([],1,[1,1]))   = (B,([0,0],1,[]))
  U11 k-mid     wsteps T T 7 (B,([0],1,[0,0]))  = (C,([],0,[1,1,0]))
  U12 k-walk    wsteps T T 3 (C,([0],0,[1]))    = (C,([],0,[1,0]))
  U13 k-fin     wsteps T T 3 (C,([1],0,[1]))    = (C,([],1,[1,0]))
  U14 k-mid-ov  wsteps T F 7 (B,([0],1,[0]))    = (C,([],0,[1,1,0]))
  U15 event     wsteps F T 5 (C,([1,0,1],1,[])) = (C,([],1,[1,0,1]))
"""
import sys

A, B, C, D = 0, 1, 2, 3
LAB = "ABCD"

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

TAB = parse("1RB0LD_0LC0RB_1RA1LD_1RB1LC")

def cstep(cfg):
    q, l, h, r = cfg
    e = TAB[(q, h)]
    if e is None: return None
    w, d, ns = e
    if d > 0: return (ns, [w] + l, r[0] if r else 0, r[1:])
    return (ns, l[1:], l[0] if l else 0, [w] + r)

class Wall(Exception): pass

def wsteps(bl, br, q, l, h, r, n):
    l, r = list(l), list(r)
    for _ in range(n):
        e = TAB[(q, h)]
        if e is None: raise Wall("halt")
        w, d, ns = e
        if d > 0:
            if not r and br: raise Wall("right")
            q, l, h, r = ns, [w] + l, (r[0] if r else 0), r[1:]
        else:
            if not l and bl: raise Wall("left")
            q, l, h, r = ns, l[1:], (l[0] if l else 0), [w] + r
    return (q, l, h, r)

STEPS = 0

def rep(u, k): return list(u) * k

def take(lst, pat, what):
    assert lst[:len(pat)] == list(pat), \
        f"{what}: want prefix {pat}, got {lst[:len(pat)]} (len {len(lst)})"
    return lst[len(pat):]

def unit(bl, br, n, q, lw, h, rw, q2, lw2, h2, rw2, name):
    got = wsteps(bl, br, q, lw, h, rw, n)
    assert got == (q2, list(lw2), h2, list(rw2)), f"{name}: unit gives {got}"

def conc(cfg, bl, br, n, lw, rw, q2, lw2, h2, rw2, name):
    """Apply unit lemma (q,(lw,h,rw)) -n-> (q2,(lw2,h2,rw2)) by transport."""
    global STEPS
    q, l, h, r = cfg
    unit(bl, br, n, q, lw, h, rw, q2, lw2, h2, rw2, name)
    lrest = take(l, lw, name + ":l")
    rrest = take(r, rw, name + ":r")
    if not bl: assert lrest == [], f"{name}: lwall off needs full l"
    if not br: assert rrest == [], f"{name}: rwall off needs full r"
    STEPS += n
    return (q2, list(lw2) + lrest, h2, list(rw2) + rrest)

def cycR(cfg, u, w, P, k, name):
    global STEPS
    q, l, h, r = cfg
    unit(True, True, P, q, [], h, u, q, w, h, [], name)
    r2 = take(r, rep(u, k), name)
    STEPS += P * k
    return (q, rep(w, k) + l, h, r2)

def cycL(cfg, u, rw, w, P, k, name):
    global STEPS
    q, l, h, r = cfg
    unit(True, True, P, q, u, h, rw, q, [], h, list(rw) + list(w), name)
    l2 = take(l, rep(u, k), name)
    r2 = take(r, rw, name + ":rw")
    STEPS += P * k
    return (q, l2, h, list(rw) + rep(w, k) + r2)

# ----------------------------------------------------------------- tapes ---
def bits(a):
    out = []
    while a: out.append(a & 1); a >>= 1
    return out

def W(a):
    out = []
    for b in bits(a): out += [0, b]
    return out

def C_conf(a):
    t = [1, 1, 0] * a + W(a)
    return (C, [], t[0], t[1:])

LU = [1, 0, 1]
RC = [1, 1, 0]

def cview(a):
    """(j, q) with q=None for overflow: a = 2^j - 1, else a = (2^j)(2q) + 2^j-1."""
    j = 0
    while (a >> j) & 1: j += 1
    q = a >> (j + 1)
    return (j, None if q == 0 and (a >> j) == 0 else q) if False else \
           (j, None if a == (1 << j) - 1 else a >> (j + 1))

# ------------------------------------------------------------------- lap ---
def lap(a):
    global STEPS
    STEPS = 0
    assert a >= 2
    j, q = cview(a)
    ov = q is None
    Wp = W(a)
    Wq = None if ov else W(q) if q >= 1 else None
    # W decomposition lemmas:
    if ov:
        assert Wp == rep([0, 1], j), "W-ov"
        Wsucc = rep([0, 0], j) + [0, 1]
    else:
        assert q >= 1, "interior q>=1"
        assert Wp == rep([0, 1], j) + [0, 0] + Wq, "W-int"
        Wsucc = rep([0, 0], j) + [0, 1] + Wq
    assert W(a + 1) == Wsucc, "W-succ"

    cfg = C_conf(a)
    assert [cfg[2]] + cfg[3] == rep([1, 1, 0], a) + Wp, "shape"
    assert cfg[3] == rep(LU, a - 1) + [1, 0] + Wp, "shape-rot"

    # S1
    cfg = conc(cfg, False, True, 2, [], [], B, [1], 1, [], "U1")
    cfg = cycR(cfg, LU, RC, 5, a - 1, "U2/S1")
    cfg = conc(cfg, True, True, 6, [], [1, 0, 0], C, [1, 0], 1, [0], "U3")
    # l = [1,0]+rep(RC,a-1)+[1] == rep(LU,a-1)+[1,0,1]  (rotation)
    ll = cfg[1]
    assert ll == [1, 0] + rep(RC, a - 1) + [1] == rep(LU, a - 1) + [1, 0, 1]
    cfg = cycL(cfg, LU, [], LU, 5, a - 1, "U4/S1")
    cfg = conc(cfg, False, True, 7, [1, 0, 1], [], B, [1], 1, [1, 0, 1], "U5/S1")
    # r = [1,0,1]+rep(LU,a-1)+W p = rep(LU,a)+W p
    # S2
    cfg = cycR(cfg, LU, RC, 5, a, "U2/S2")
    # (B, rep(RC,a)+[1], 1, W p);  L0 := rep(RC,a)+[1]
    if not ov:
        cfg = cycR(cfg, [0, 1], [1, 1], 4, j, "U6")
        # r = [0,0]+W q = [0,0,0]+Wq[1:]
        cfg = conc(cfg, True, True, 5, [], [0, 0, 0], C, [1], 1, [0, 0], "U7")
        # l = [1]+rep([1,1],j)+L0 = rep([1,1],j+1)+tlL0
        assert cfg[1] == rep([1, 1], j + 1) + [1, 0] + rep(RC, a - 1) + [1]
        cfg = cycL(cfg, [1, 1], [], [1, 1], 2, j + 1, "U8")
        # (C, tl L0, 1, rep([1,1],j+1)+[0,0]+Wq[1:])
    else:
        cfg = cycR(cfg, [0, 1], [1, 1], 4, j, "U6-ov")
        cfg = conc(cfg, True, False, 5, [], [], C, [1], 1, [0], "U9")
        assert cfg[1] == rep([1, 1], j + 1) + [1, 0] + rep(RC, a - 1) + [1]
        cfg = cycL(cfg, [1, 1], [], [1, 1], 2, j + 1, "U8-ov")
        # (C, tl L0, 1, rep([1,1],j+1)+[0])
    assert cfg[1] == rep(LU, a - 1) + [1, 0, 1]
    cfg = cycL(cfg, LU, [], LU, 5, a - 1, "U4/S2")
    cfg = conc(cfg, False, True, 7, [1, 0, 1], [], B, [1], 1, [1, 0, 1], "U5/S2")
    # S3
    cfg = cycR(cfg, LU, RC, 5, a, "U2/S3")
    # (B, L0, 1, dirty)
    cfg = cycR(cfg, [1, 1], [0, 0], 2, j + 1, "U10")
    if not ov:
        # r = [0,0]+Wq[1:] = [0,0]+Wq[1:] ; U11 needs [0,0] window
        cfg = conc(cfg, True, True, 7, [0], [0, 0], C, [], 0, [1, 1, 0], "U11")
    else:
        cfg = conc(cfg, True, False, 7, [0], [0], C, [], 0, [1, 1, 0], "U14")
    # l = rep([0],2j+1)+L0 ; r = [1,1,0]+(Wq[1:] | [])
    cfg = cycL(cfg, [0], [1], [0], 3, 2 * j + 1, "U12")
    cfg = conc(cfg, True, True, 3, [1], [1], C, [], 1, [1, 0], "U13")
    # (C, tl L0, 1, [1,0]+[0]^(2j+1)+[1,0]+(Wq[1:]|[]))
    #   = (C, tl L0, 1, [1,0]+W(a+1)(+[0] if ov))
    got_r = cfg[3]
    want = [1, 0] + Wsucc + ([0] if ov else [])
    assert got_r == want, f"k-exit r: {got_r} vs {want}"
    assert cfg[1] == rep(LU, a - 1) + [1, 0, 1]
    cfg = cycL(cfg, LU, [], LU, 5, a - 1, "U4/S3")
    cfg = conc(cfg, False, True, 5, [1, 0, 1], [], C, [], 1, [1, 0, 1], "U15")
    return STEPS, cfg

# --------------------------------------------------------------- raw+diff --
def raw_lap(a):
    cfg = C_conf(a)
    for n in range(1, 4000 * a + 40000):
        cfg = cstep(cfg)
        if cfg is None: return None
        q, l, h, r = cfg
        if q == C and h == 1 and all(x == 0 for x in l):
            tape = [h] + r
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

def norm(cfg):
    q, l, h, r = cfg
    l, r = list(l), list(r)
    while l and l[-1] == 0: l.pop()
    while r and r[-1] == 0: r.pop()
    return (q, l, h, r)

def visits_check(a):
    """States at csteps 0,1,2,6 from C(a) must be C,D,B,A."""
    cfg = C_conf(a)
    seen = {0: cfg[0]}
    for k in range(1, 7):
        cfg = cstep(cfg)
        seen[k] = cfg[0]
    return seen[0] == C and seen[1] == D and seen[2] == B and seen[6] == A

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    bad = 0
    for a in range(2, hi + 1):
        try:
            n_sym, cfg_sym = lap(a)
        except (AssertionError, Wall) as e:
            print(f"a={a}: SYMBOLIC FAIL: {e}")
            bad += 1
            if bad > 5: sys.exit(1)
            continue
        n_raw, cfg_raw = raw_lap(a)
        ok = (n_sym == n_raw and norm(cfg_sym) == norm(cfg_raw)
              and norm(cfg_sym) == norm(C_conf(a + 1)) and visits_check(a))
        if not ok:
            print(f"a={a}: steps sym={n_sym} raw={n_raw} "
                  f"cfg={'OK' if norm(cfg_sym)==norm(cfg_raw) else 'BAD'} "
                  f"Ca1={'OK' if norm(cfg_sym)==norm(C_conf(a+1)) else 'BAD'} "
                  f"visits={visits_check(a)}")
            bad += 1
            if bad > 5: sys.exit(1)
    print(f"a=2..{hi}: {'ALL OK' if bad == 0 else f'{bad} FAILURES'}")
