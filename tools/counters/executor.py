#!/usr/bin/env python3
"""Parametric symbolic-lap executor for the mono_counter family.

Combinators identical to symlap10_v2 (mirroring the Coq toolkit); each
machine supplies a skeleton = the ordered phase list.  Units are DERIVED
(wsteps on the declared window) and printed for Coq transcription.
"""
import sys

LAB = "ABCD"

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

class Wall(Exception): pass

class Exec:
    def __init__(self, spec):
        self.tab = parse(spec)
        self.steps = 0
        self.units = {}   # name -> (bl, br, n, entry, exit)

    def cstep(self, cfg):
        q, l, h, r = cfg
        e = self.tab[(q, h)]
        if e is None: return None
        w, d, ns = e
        if d > 0: return (ns, [w] + l, r[0] if r else 0, r[1:])
        return (ns, l[1:], l[0] if l else 0, [w] + r)

    def wsteps(self, bl, br, q, l, h, r, n):
        l, r = list(l), list(r)
        for _ in range(n):
            e = self.tab[(q, h)]
            if e is None: raise Wall("halt")
            w, d, ns = e
            if d > 0:
                if not r and br: raise Wall("right")
                q, l, h, r = ns, [w] + l, (r[0] if r else 0), r[1:]
            else:
                if not l and bl: raise Wall("left")
                q, l, h, r = ns, l[1:], (l[0] if l else 0), [w] + r
        return (q, l, h, r)

    def record(self, name, bl, br, n, entry, out):
        prev = self.units.get(name)
        cur = (bl, br, n, entry, out)
        assert prev is None or prev == cur, f"{name}: unit varies!\n {prev}\n {cur}"
        self.units[name] = cur

    def conc(self, cfg, bl, br, n, lwin, rwin, name):
        q, l, h, r = cfg
        lw = len(l) if lwin is None else lwin
        rw = len(r) if rwin is None else rwin
        if not bl: assert lw == len(l), f"{name}: lwall off needs whole l"
        if not br: assert rw == len(r), f"{name}: rwall off needs whole r"
        out = self.wsteps(bl, br, q, l[:lw], h, r[:rw], n)
        self.record(name, bl, br, n, (q, tuple(l[:lw]), h, tuple(r[:rw])),
                    (out[0], tuple(out[1]), out[2], tuple(out[3])))
        self.steps += n
        return (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:])

    def cycR(self, cfg, ulen, P, k, name):
        """unit consumes ulen cells of r; derive u and w."""
        if k == 0: return cfg
        q, l, h, r = cfg
        u = r[:ulen]
        out = self.wsteps(True, True, q, [], h, u, P)
        q2, w, h2, rr = out
        assert q2 == q and h2 == h and rr == [], f"{name}: not a cycR unit: {out}"
        self.record(name, True, True, P, (q, (), h, tuple(u)),
                    (q, tuple(w), h, ()))
        assert r[:ulen*k] == u * k, f"{name}: r not u^k"
        self.steps += P * k
        return (q, w * k + l, h, r[ulen*k:])

    def cycL(self, cfg, ulen, rwlen, P, k, name):
        if k == 0: return cfg
        q, l, h, r = cfg
        u, rw = l[:ulen], r[:rwlen]
        out = self.wsteps(True, True, q, u, h, rw, P)
        q2, ll, h2, rout = out
        assert q2 == q and h2 == h and ll == [] and rout[:rwlen] == rw, \
            f"{name}: not a cycL unit: {out}"
        w = rout[rwlen:]
        self.record(name, True, True, P, (q, tuple(u), h, tuple(rw)),
                    (q, (), h, tuple(rout)))
        assert l[:ulen*k] == u * k, f"{name}: l not u^k"
        self.steps += P * k
        return (q, l[ulen*k:], h, rw + w * k + r[rwlen:])

    def dump_units(self):
        for name, (bl, br, n, e, o) in self.units.items():
            fe = f"({LAB[e[0]]},{list(e[1])},{e[2]},{list(e[3])})"
            fo = f"({LAB[o[0]]},{list(o[1])},{o[2]},{list(o[3])})"
            print(f"  {name:10s} bl={int(bl)} br={int(br)} n={n}: {fe} -> {fo}")

# ---------------------------------------------------------------- family ---
def bits(a):
    out = []
    while a: out.append(a & 1); a >>= 1
    return out

def W(a):
    out = []
    for b in bits(a): out += [0, b]
    return out

def carry(a):
    j = 0
    while (a >> j) & 1: j += 1
    return j, (a == (1 << j) - 1)

def rep(u, k): return list(u) * k

def norm(cfg):
    q, l, h, r = cfg
    l, r = list(l), list(r)
    while l and l[-1] == 0: l.pop()
    while r and r[-1] == 0: r.pop()
    return (q, l, h, r)
