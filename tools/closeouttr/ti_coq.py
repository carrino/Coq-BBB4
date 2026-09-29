"""Exact Python mirror of the decidable parts of theories/Counters/TriGlueTr.v
(UNTRUSTED: the kernel re-checks everything; this module only lets the
finder emit certificates the checker accepts).

Affine expressions: (c, ((k, a), ...)) with the terms sorted by variable,
positive coefficients.  Segments: ('L', syms) / ('B', unit, aexp); sides are
nearest-first.  Every function here transcribes its Coq namesake.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))
import lapcert as LC   # noqa: E402

# ---------------------------------------------------------------- aexp ----


def aconst(n):
    return (n, ())


def tins(k, a, t):
    t = list(t)
    for i, (k2, a2) in enumerate(t):
        if k < k2:
            return tuple(t[:i] + [(k, a)] + t[i:])
        if k == k2:
            return tuple(t[:i] + [(k, a + a2)] + t[i + 1:])
    return tuple(t + [(k, a)])


def tadd(t1, t2):
    acc = tuple(t2)
    for k, a in reversed(t1):
        if a != 0:
            acc = tins(k, a, acc)
    return acc


def tscale(m, t):
    if m == 0:
        return ()
    return tuple((k, m * a) for k, a in t)


def aadd(e1, e2):
    return (e1[0] + e2[0], tadd(e1[1], e2[1]))


def aaddc(e, n):
    return (e[0] + n, e[1])


def ascale(m, e):
    return (m * e[0], tscale(m, e[1]))


def tsubst(s, t):
    if not t:
        return aconst(0)
    (k, a), rest = t[0], t[1:]
    x = s[k] if k < len(s) else aconst(0)
    return aadd(ascale(a, x), tsubst(s, rest))


def asubst(s, e):
    return aaddc(tsubst(s, e[1]), e[0])


def aeval(v, e):
    return e[0] + sum(a * (v[k] if k < len(v) else 0) for k, a in e[1])


def tcoef(k, t):
    return sum(a for k2, a in t if k2 == k)


def tbound(t):
    return max([k + 1 for k, _ in t] + [0])


def ale(e1, e2):
    n = max(tbound(e1[1]), tbound(e2[1]))
    return e1[0] <= e2[0] and all(tcoef(k, e1[1]) <= tcoef(k, e2[1]) for k in range(n))


# ------------------------------------------------------------- segments ----

def rep(u, n):
    return tuple(u) * n


def segd(v, s):
    return tuple(s[1]) if s[0] == 'L' else rep(s[1], aeval(v, s[2]))


def sided(v, l):
    out = ()
    for s in l:
        out += segd(v, s)
    return out


def seg_subst(sub, x):
    return x if x[0] == 'L' else ('B', x[1], asubst(sub, x[2]))


def primroot(u):
    u = tuple(u)
    n = len(u)
    d = 1
    for _ in range(n):
        if n % d == 0 and rep(u[:d], n // d) == u:
            return u[:d], n // d
        d += 1
    return u, 1


def strip(p, l):
    if tuple(l[:len(p)]) == tuple(p) and len(l) >= len(p):
        return tuple(l[len(p):])
    return None


def strip_suf(v, l):
    k = max(len(l) - len(v), 0)
    if tuple(l[k:]) == tuple(v):
        return tuple(l[:k])
    return None


def cpre(u, w):
    n = 0
    w = tuple(w)
    for _ in range(len(w)):
        if not u:
            break
        w2 = strip(u, w)
        if w2 is None:
            break
        n += 1
        w = w2
    return n, w


def csuf(u, w):
    n = 0
    w = tuple(w)
    for _ in range(len(w)):
        if not u:
            break
        w2 = strip_suf(u, w)
        if w2 is None:
            break
        n += 1
        w = w2
    return n, w


def push_blk2(acc, u, e):
    if acc and acc[0][0] == 'B':
        _, u2, e2 = acc[0]
        if tuple(u2) == tuple(u):
            return [('B', u, aadd(e2, e))] + acc[1:]
    return [('B', u, e)] + acc


def push_blk(acc, u, e):
    if not acc:
        return [('B', u, e)]
    top = acc[0]
    if top[0] == 'B':
        if tuple(top[1]) == tuple(u):
            return [('B', u, aadd(top[2], e))] + acc[1:]
        return [('B', u, e)] + acc
    w0 = top[1]
    n, w0p = csuf(u, w0)
    if n == 0:
        return [('B', u, e)] + acc
    if not w0p:
        return push_blk2(acc[1:], u, aaddc(e, n))
    return [('B', u, aaddc(e, n)), ('L', w0p)] + acc[1:]


def push_lit2(acc, w):
    if acc and acc[0][0] == 'B':
        _, u, e = acc[0]
        n, wp = cpre(u, w)
        if not wp:
            return [('B', u, aaddc(e, n))] + acc[1:]
        return [('L', wp), ('B', u, aaddc(e, n))] + acc[1:]
    return [('L', tuple(w))] + acc


def push_lit(acc, w):
    if not w:
        return acc
    if acc and acc[0][0] == 'L':
        return push_lit2(acc[1:], tuple(acc[0][1]) + tuple(w))
    return push_lit2(acc, w)


def push(acc, x):
    if x[0] == 'L':
        return push_lit(acc, tuple(x[1]))
    v, p = primroot(x[1])
    e2 = ascale(p, x[2])
    if not v:
        return acc
    if not e2[1]:
        return push_lit(acc, rep(v, e2[0]))
    return push_blk(acc, v, e2)


def norm(l):
    acc = []
    for x in l:
        acc = push(acc, x)
    return list(reversed(acc))


def drop_blanks(w):
    i = 0
    while i < len(w) and w[i] == 0:
        i += 1
    return tuple(w[i:])


def rstrip0(w):
    return tuple(reversed(drop_blanks(tuple(reversed(w)))))


def nstrip_r(l):
    while l:
        x = l[0]
        if x[0] == 'L':
            w = rstrip0(x[1])
            if not w:
                l = l[1:]
                continue
            return [('L', w)] + l[1:]
        if all(s == 0 for s in x[1]):
            l = l[1:]
            continue
        return l
    return []


def nstrip(l):
    return list(reversed(nstrip_r(list(reversed(l)))))


def segs_eq(l1, l2):
    if len(l1) != len(l2):
        return False
    for x, y in zip(l1, l2):
        if x[0] != y[0]:
            return False
        if x[0] == 'L':
            if tuple(x[1]) != tuple(y[1]):
                return False
        elif tuple(x[1]) != tuple(y[1]) or x[2] != y[2]:
            return False
    return True


def same_segs(l1, l2):
    return segs_eq(norm(l1), norm(l2))


def lsame_segs(l1, l2):
    return segs_eq(nstrip(norm(l1)), nstrip(norm(l2)))


def ss_segs(s, j):
    pre, u, a, b, post = s
    return [('L', tuple(pre)), ('B', tuple(u), (b, ((j, a),) if a else ())), ('L', tuple(post))]


# ---------------------------------------------------------------- walk ----

def reg1(k, Mc):
    M, c = Mc
    return (c, ((k, M),) if M else ())


def rsub(R):
    return [reg1(k, Mc) for k, Mc in enumerate(R)]


def twalk(nodes, fuel, i, R, z):
    R, z = list(R), list(z)
    for _ in range(fuel):
        if i >= len(nodes):
            return None
        nd = nodes[i]
        if nd[0] == 'leaf':
            return nd[1], R, z
        _, k, n, p, kids = nd
        zk = z[k] if k < len(z) else 0
        M, c = R[k] if k < len(R) else (0, 0)
        if zk < n:
            if zk >= len(kids):
                return None
            i = kids[zk]
            if k < len(R):
                R[k] = (0, c + M * zk)
            if k < len(z):
                z[k] = 0
        else:
            s = (zk - n) % p if p else zk - n
            q = (zk - n) // p if p else 0
            if n + s >= len(kids):
                return None
            i = kids[n + s]
            if k < len(R):
                R[k] = (M * p, c + M * (n + s))
            if k < len(z):
                z[k] = q
    return None


def tleaves(nodes, fuel, i, R):
    if fuel == 0 or i >= len(nodes):
        return None
    nd = nodes[i]
    if nd[0] == 'leaf':
        return [(nd[1], list(R))]
    _, k, n, p, kids = nd
    if p == 0 or len(kids) != n + p or not k < len(R):
        return None
    M, c = R[k]
    out = []
    for j, i2 in enumerate(kids):
        R2 = list(R)
        R2[k] = (0, c + M * j) if j < n else (M * p, c + M * j)
        r = tleaves(nodes, fuel - 1, i2, R2)
        if r is None:
            return None
        out += r
    return out


# ------------------------------------------------------------ liveness ----

def zsub(P, s):
    return [(x, ((k, P),)) for k, x in enumerate(s)]


def pdiv(P, e):
    return all(a % P == 0 for _, a in e[1])


def compat1(P, Mc, e):
    M, c = Mc
    if not e[1]:
        if M == 0:
            return e[0] == c
        return c <= e[0] and (e[0] - c) % M == 0
    if M == 0:
        return e[0] <= c and (c - e[0]) % P == 0
    if P % M == 0:
        return e[0] % M == c % M
    return True


def compat(P, R, tgt):
    if len(R) != len(tgt):
        return False
    return all(compat1(P, Mc, e) for Mc, e in zip(R, tgt))


def sassign(P, R, rho):
    if not R:
        return [[]]
    if not rho:
        return []
    (M, c), R2 = R[0], R[1:]
    out = []
    rest = sassign(P, R2, rho[1:])
    for s in range(P):
        if (M * s + c) % P == rho[0]:
            out += [[s] + r for r in rest]
    return out


def veval(V, xs):
    c, vs = V
    acc = aconst(c)
    for a, x in reversed(list(zip(vs, xs))):
        acc = aadd(ascale(a, x), acc)
    return acc


# ------------------------------------------------------------- chains ----

def cuts(st):
    if st[0] in ('SWin', 'SWinL', 'SWinR'):
        return [(st[0], m) for m in range(1, st[1] + 1)]
    return [st]


def prefs(l):
    if not l:
        return [[]]
    st = l[0]
    return [[]] + [[x] for x in cuts(st)] + [[st] + p for p in prefs(l[1:])]


def leaf_fired(tabw, lf):
    out = []
    for pr in prefs(lf['chain']):
        try:
            r = LC.srun(tabw, lf['el'], lf['er'], pr, lf['c0'])
        except LC.Halt:
            r = None
        if r is not None:
            c1 = r[0]
            out.append((c1[0], c1[2]))
    return out
