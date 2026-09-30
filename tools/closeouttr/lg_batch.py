#!/usr/bin/env python3
"""Block-LIST glue (UNTRUSTED finder + batch writer) for
theories/Counters/ListGlueTr.v, SCOPING_INSTR.md §7.4.BLC.

    python3 tools/closeouttr/lg_batch.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/lg_batch.py batch OUT.jsonl [...] --tag BLC [--chunk 10]

The rows of §7.4.BL piece (a) keep a LIST of blocks whose lengths follow a
neighbour recurrence ([b_(i+1) = a b_i + d_i], the offset [d_i] a finite
digit).  TriGlueTr's families are whole symbolic tapes with a fixed number of
blocks; on these rows the block count grows, and TI stops at "too many
families".  Here a family is a TriGlue family (the WINDOW: literal words and
blocks with affine exponents) plus, on each side, an optional TAIL: a list of
ITEMS [pre u^e] (nearest-first) accepted by an automaton whose transitions
carry the neighbour relation of an item to the one before it:

    up   (a, d):  e      = a * e_prev + d
    down (a, d):  e_prev = a * e      + d      (a = 0: e_prev = d and e = 0)

The first item relates to the family's REF, an affine expression over the
family's variables.  A leaf of a family may UNFOLD tail items into its window
(a dispatch on the tail's first item: which transition it takes), runs ONE
LapDecider chain on the window (the tail is the chain's opaque rest), and
lands on a family whose window may FOLD its outermost items back into the
tail.  Every relation is an identity of affine forms, checked coefficient
by coefficient.  Liveness: TriGlue's (leaf, residue) nodes, with rankings
that add a per-kind affine weight [alpha e + beta] for every tail item.

`find` builds the certificate by symbolic execution from a boot tape (as
ti_batch.py, which it extends), learning the item kinds and the automaton
while it explores; every check of the kernel checker is replayed in Python
before a certificate is written.  The kernel re-checks everything: a wrong
certificate fails to compile, it cannot mis-prove.
"""
import argparse
import collections
import json
import math
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ti_batch as T                            # noqa: E402
import ti_coq as C                              # noqa: E402

LC = C.LC
Fail, Req = T.Fail, T.Req

MAXFAM = 200
MAXLEAF = 3000
MAXSTEPS = 60000
CUTSTEPS = 400
MAXNA = 8
MAXNFA = 400
MAXROUNDS = 20000
MAXUNF = 3
VERBOSE = bool(os.environ.get('LG_VERBOSE'))
T0S = (20000, 100000)
PLIST = (1, 2)
KEEP = 1            # blocks kept in the window on a tail side
MAXD = 16           # largest offset of a relation guessed from two constants
BOOT_AMAX = 4

# ------------------------------------------------------------- aexps ----


def aeq(e1, e2):
    return C.ale(e1, e2) and C.ale(e2, e1)


def acoefs(e):
    return [(k, a) for k, a in e[1] if a]


def aadd_int(e, d):
    """e + d for an integer d; None if the constant would go negative"""
    c = e[0] + d
    if c < 0:
        return None
    return (c, e[1])


def rel_ok(rel, p, e):
    """the relation as an identity of aexps p (pred) and e (item)"""
    up, a, d = rel
    if up:
        # e = a p + d
        lhs = C.ascale(a, p)
        return aeq(C.aaddc(lhs, max(d, 0)), C.aaddc(e, max(-d, 0)))
    if a == 0:
        return (not acoefs(p)) and p[0] == d and (not acoefs(e)) and e[0] == 0
    rhs = C.ascale(a, e)
    return aeq(C.aaddc(p, max(-d, 0)), C.aaddc(rhs, max(d, 0)))


def rel_num(rel, p, e):
    up, a, d = rel
    if up:
        return e == a * p + d
    if a == 0:
        return p == d and e == 0
    return p == a * e + d


def rel_bound(rel, md):
    """the least pred of an item that satisfies rel with an exponent >= md"""
    up, a, d = rel
    INF = float('inf')
    if md == INF:
        return INF
    if up:
        if a == 0:
            return 0 if d >= md else INF
        need = md - d
        return max(0, -(-need // a))
    if a == 0:
        return d if md == 0 else INF
    return max(0, a * md + d)


def rel_apply(rel, p):
    """the item exponent from the pred aexp p: an aexp, 'void' (no item can
    satisfy it), or ('mod', k, a) / ('ge', k, n) (the region must be refined)"""
    up, a, d = rel
    cs = acoefs(p)
    if up:
        e = (a * p[0] + d, tuple((k, a * m) for k, m in cs) if a else ())
        if e[0] < 0:
            if not e[1]:
                return 'void'
            k, m = e[1][0]
            return ('ge', k, -(e[0]) // m + (1 if (-(e[0])) % m else 0))
        return e
    if a == 0:
        if not cs:
            return (0, ()) if p[0] == d else 'void'
        k, m = cs[0]
        if d < p[0]:
            return 'void'
        if len(cs) > 1:
            return ('ge', k, (d - p[0]) // m + 1)
        if (d - p[0]) % m:
            return 'void'
        return ('ge', k, (d - p[0]) // m + 1)
    for k, m in cs:
        if m % a:
            return ('mod', k, a)
    c = p[0] - d
    if c % a:
        return 'void'
    if c < 0:
        if not cs:
            return 'void'
        k, m = cs[0]
        need = -c
        return ('ge', k, need // m + (1 if need % m else 0))
    return (c // a, tuple((k, m // a) for k, m in cs))


RATIO = [2]


def infer_rel(p, e):
    """a relation making (p, e) an identity, or None"""
    cp, ce = acoefs(p), acoefs(e)
    if not cp and not ce:
        # both constant: the list ratio (so the relation generalises)
        a = RATIO[0]
        if p[0] >= e[0]:
            return (False, a, p[0] - a * e[0])
        return (True, a, e[0] - a * p[0])
    if not ce:
        return (True, 0, e[0])
    if not cp:
        return None
    dp, de = dict(cp), dict(ce)
    if set(dp) != set(de):
        return None
    ks = sorted(dp)
    k0 = ks[0]
    if de[k0] % dp[k0] == 0:
        a = de[k0] // dp[k0]
        if all(de[k] == a * dp[k] for k in ks):
            return (True, a, e[0] - a * p[0])
    if dp[k0] % de[k0] == 0:
        a = dp[k0] // de[k0]
        if all(dp[k] == a * de[k] for k in ks):
            return (False, a, p[0] - a * e[0])
    return None


# --------------------------------------------------------- automaton ----

def shift_rel(rel, dl):
    """the relation to pred p of an item whose true pred is p + dl"""
    up, a, d = rel
    if up:
        return (True, a, d + a * dl) if a else rel
    return (False, a, d - dl)


class NFA:
    """item kinds and transitions, learned during the exploration.  A state is
    ('S', unit of the item read last, offset): the tail after it is valid
    from ('S', unit, 0) with the pred shifted by the offset (the explicit
    shifted copies of the transitions are generated here)"""

    def __init__(self):
        self.kinds = []         # (side, pre, u)
        self.kidx = {}
        self.trans = []         # (side, src, kind, dst, rel)
        self.tidx = {}
        self.acc = set()        # (side, state)
        self.version = 0
        self.touched = set()    # (side, state) whose out-set changed
        self.shifts = collections.defaultdict(set)   # (side, unit) -> offsets

    def kind(self, side, pre, u):
        key = (side, tuple(pre), tuple(u))
        if key not in self.kidx:
            self.kidx[key] = len(self.kinds)
            self.kinds.append(key)
        return self.kidx[key]

    def _add(self, key):
        if key not in self.tidx:
            if len(self.trans) >= MAXNFA:
                raise Fail('automaton too large')
            self.tidx[key] = len(self.trans)
            self.trans.append(key)
            self.version += 1
            self.touched.add((key[0], key[1]))
        return self.tidx[key]

    def learn(self, side, src, k, rel, dst=None):
        if dst is None:
            dst = ('S', self.kinds[k][2], 0)
        ti = self._add((side, src, k, dst, rel))
        if src[2] == 0:
            for dl in list(self.shifts[(side, src[1])]):
                self._add((side, ('S', src[1], dl), k, dst, shift_rel(rel, dl)))
        return ti

    def ensure_shift(self, side, u, dl):
        st = ('S', tuple(u), dl)
        if dl == 0 or dl in self.shifts[(side, tuple(u))]:
            return st
        self.shifts[(side, tuple(u))].add(dl)
        base = ('S', tuple(u), 0)
        for t in list(self.trans):
            if t[0] == side and t[1] == base:
                self._add((side, st, t[2], t[3], shift_rel(t[4], dl)))
        if (side, base) in self.acc:
            self.accept(side, st)
        return st

    def accept(self, side, s):
        for s2 in [s] + ([('S', s[1], dl) for dl in self.shifts[(side, s[1])]] if s[2] == 0 else []):
            if (side, s2) not in self.acc:
                self.acc.add((side, s2))
                self.version += 1
                self.touched.add((side, s2))

    def mins(self):
        """per (side, state): the least ref a valid tail allows (a fixpoint;
        the checker verifies it as a lower bound)"""
        INF = float('inf')
        states = set(self.acc) | set((t[0], t[1]) for t in self.trans) | \
            set((t[0], t[3]) for t in self.trans)
        m = {st: (0 if st in self.acc else INF) for st in states}
        for _ in range(len(states) * 64 + 64):
            ch = False
            for (sd, src, k, dst, rel) in self.trans:
                b = rel_bound(rel, m[(sd, dst)])
                if b < m[(sd, src)]:
                    m[(sd, src)] = b
                    ch = True
            if not ch:
                break
        return m

    def out(self, side, s):
        return [i for i, t in enumerate(self.trans) if t[0] == side and t[1] == s]


def state_of_unit(u):
    return ('S', tuple(u), 0)


def item_segs(nfa, k, e):
    side, pre, u = nfa.kinds[k]
    return [('L', tuple(pre)), ('B', tuple(u), e)]


# ---------------------------------------------------------------- leaf ----

def leaf_run(tabw, q, h, Lz, Rz, endL, endR, na, p):
    """ti_batch.leaf_run on explicit (substituted) window sides; reaching the
    end of a side whose tail is not known empty asks for an unfold"""
    tr = tabw.get((q, h))
    if tr is None:
        raise Fail('pinned at a family start')
    D = 'R' if tr[1] > 0 else 'L'
    Dz, Oz = (Rz, Lz) if D == 'R' else (Lz, Rz)
    dpre, i = T.cprefix(Dz, 0)
    idx = None
    if not dpre and i < len(Dz) and Dz[i][0] == 'B':
        u, e = tuple(Dz[i][1]), Dz[i][2]
        if len(e[1]) != 1:
            raise Fail('multi-variable block')
        (k, a), c = e[1][0], e[0]
        if c < na:
            raise Req('ge', k, na - c)
        if p > 1 and a % p:
            raise Req('mod', k, p)
        b, r = divmod(c - na, p)
        post, i2 = T.cprefix(Dz, i + 1)
        dss = (C.rep(u, na), C.rep(u, p), a // p, b, C.rep(u, r) + post)
        nD = i2
        idx = (k, D, u)
    else:
        dss = (dpre, (), 0, 0, ())
        nD = i
    opre, nO = T.cprefix(Oz, 0)
    oss = (opre, (), 0, 0, ())
    if D == 'R':
        c0 = (q, oss, h, dss)
        nL, nR = nO, nD
    else:
        c0 = (q, dss, h, oss)
        nL, nR = nD, nO
    el, er = nL >= len(Lz) and endL, nR >= len(Rz) and endR
    j = idx[0] if idx else 0
    chain = []
    c = c0
    crossed = False
    nsteps = 0

    def emit(st):
        nonlocal c
        try:
            r = LC.sstep(tabw, el, er, st, c)
        except LC.Halt:
            r = None
        if r is None:
            raise Fail('sstep refused %r' % (st,))
        chain.append(st)
        c = r[0]

    lastd = None
    while True:
        if nsteps > MAXSTEPS:
            raise Fail('leaf too long')
        q1, L1, h1, R1 = c
        tr = tabw.get((q1, h1))
        if tr is None:
            raise Fail('pinned inside a leaf')
        if nsteps >= CUTSTEPS and lastd is not None and tr[1] != lastd and (crossed or idx is None):
            break                       # a long walk in literal cells: cut at a turn
        lastd = tr[1]
        if idx is not None and not crossed:
            bs = R1 if idx[1] == 'R' else L1
            if not bs[0] and bs[1]:
                if idx[1] == 'R':
                    n = T.cyc_R(tabw, q1, h1, bs[1])
                    if n is not None:
                        emit(('SCycR', n))
                        crossed = True
                        nsteps += 1
                        continue
                else:
                    r = T.cyc_L(tabw, q1, h1, bs[1], R1[0])
                    if r is not None:
                        emit(('SCycL', r[0], r[1]))
                        crossed = True
                        nsteps += 1
                        continue
        d = tr[1]
        side = R1 if d > 0 else L1
        if side[0]:
            emit(('SWin', 1))
            nsteps += 1
            continue
        if side[1]:
            if idx is not None and not crossed and ((d > 0) == (idx[1] == 'R')):
                u = idx[2]
                if p == 1:
                    for p2 in (2, 3, 4):
                        U2 = u * p2
                        ok = (T.cyc_R(tabw, q1, h1, U2) is not None) if d > 0 \
                            else T.cyc_L(tabw, q1, h1, U2, R1[0]) is not None
                        if ok:
                            raise Req('pow', idx[0], p2)
                if nsteps > 0:
                    break
                if na >= MAXNA:
                    raise Fail('no cycle through the start block')
                raise Req('na', idx[0], na + 1)
            break
        X = (Rz[nR:] if d > 0 else Lz[nL:])
        if X:
            break
        if not (endR if d > 0 else endL):
            if nsteps > 0:
                break
            raise Req('unf', 'R' if d > 0 else 'L', 0)
        emit(('SWinR', 1) if d > 0 else ('SWinL', 1))
        nsteps += 1
    if nsteps == 0:
        raise Fail('empty leaf')
    chain = T.merge_chain(chain)
    r = LC.srun(tabw, el, er, chain, c0)
    if r is None:
        raise Fail('chain does not replay')
    c1, ca, cb = r
    if cb == 0:
        if idx is None:
            raise Fail('zero-step leaf')
        raise Req('ge', idx[0], 1 + (0 if dss[3] or dss[0] else 0))
    endLs = C.ss_segs(c1[1], j) + Lz[nL:]
    endRs = C.ss_segs(c1[3], j) + Rz[nR:]
    return dict(c0=c0, el=el, er=er, chain=chain, j=j, nL=nL, nR=nR, c1=c1,
                q1=c1[0], h1=c1[2], endL=endLs, endR=endRs)


# ------------------------------------------------------------ families ----

SMALL = 7           # a boot block this short is read as literal
MINCOPY = 3         # ... and a block of a longer unit needs this many copies
LUMIN = 3           # copies that make a run of a side's list unit an item
GENZ = 3            # a run of zeros this long is a block (away from the tape end)


def gen_lit(w, strip_end, small=SMALL, units=()):
    """a literal word (nearest-first) as segments: runs of >= 2 copies of a
    unit of 1..4 cells (zeros: >= GENZ, not at the end of the word when
    [strip_end]) longer than [small] cells become constant blocks"""
    w = tuple(w)
    if strip_end:
        while w and w[-1] == 0:
            w = w[:-1]
    out, lit, i = [], [], 0
    while i < len(w):
        best = None
        for u in T.GEN_UNITS + [(0,)]:
            k = len(u)
            n = 0
            while w[i + k * n:i + k * (n + 1)] == u:
                n += 1
            lu = u in units
            if (lu and n >= LUMIN) or (n >= max(2, MINCOPY if k > 1 else 2) and k * n > small):
                if best is not None and k * n <= len(best[0]) * best[1]:
                    continue
                if u == (0,) and ((n < GENZ and not lu) or (strip_end and i + n >= len(w))):
                    continue
                best = (u, n, lu)
        if best:
            if lit:
                out.append(('L', tuple(lit)))
                lit = []
            # a short run of the side's list unit is an item of a known
            # length (constant), a long run is a block born from a literal
            out.append(('B', best[0], (best[1], ()), not (best[2] and best[1] * len(best[0]) <= small)))
            i += len(best[0]) * best[1]
        else:
            lit.append(w[i])
            i += 1
    if lit:
        out.append(('L', tuple(lit)))
    return out


def fpush(acc, x):
    """ti_coq.push, except that a constant block longer than SMALL cells
    stays a block (a length a relation fixed is not a growing literal)"""
    if x[0] == 'L':
        return C.push_lit(acc, tuple(x[1]))
    v, p = C.primroot(x[1])
    e2 = C.ascale(p, x[2])
    if not v:
        return acc
    if not e2[1] and e2[0] == 0:
        return acc
    return C.push_blk(acc, v, e2)


def fnorm(l):
    acc = []
    for x in l:
        acc = fpush(acc, x)
    return list(reversed(acc))


def gen_side(syms, small=SMALL):
    return gen_lit(syms, True, small)


def gen_segs(side, ended, units=()):
    """the literal segments of a normalized side, generalized (a trailing
    zero run of an ended side is blank)"""
    out = []
    for i, x in enumerate(side):
        if x[0] != 'L':
            out.append(x)
            continue
        out.extend(gen_lit(x[1], ended and i == len(side) - 1, SMALL, units))
    return out


def blocks_of(side):
    return [i for i, s in enumerate(side) if s[0] == 'B']


from fractions import Fraction                      # noqa: E402
import itertools                                    # noqa: E402


class Hull:
    """an affine subspace of Q^n: the affine hull of every value vector
    joined into it (Karr's affine-equality domain), and per coordinate the
    least value of a joined base point"""

    def __init__(self, n):
        self.n = n
        self.base = None
        self.rows = []            # echelon basis: (pivot, vector of Fractions)
        self.mins = [None] * n

    def _add_dir(self, v):
        v = [Fraction(x) for x in v]
        for piv, r in self.rows:
            if v[piv]:
                f = v[piv] / r[piv]
                v = [a - f * b for a, b in zip(v, r)]
        for i, x in enumerate(v):
            if x:
                self.rows.append((i, v))
                return True
        return False

    def add(self, e0, ks):
        ch = False
        for i, x in enumerate(e0):
            if self.mins[i] is None or x < self.mins[i]:
                self.mins[i] = x
                ch = True
        if self.base is None:
            self.base = list(e0)
            ch = True
        elif self._add_dir([a - b for a, b in zip(e0, self.base)]):
            ch = True
        for k in ks:
            if self._add_dir(k):
                ch = True
        return ch

    def dim(self):
        return len(self.rows)

    def param(self, isref=()):
        """(B, lam, cst, lb): coordinates B cover the hull (every other
        coordinate j is cst_j + sum lam[j][i] (lb_i + x_i) on it, lam
        nonnegative integers, cst_j >= 0), lb_i the least joined value of B_i"""
        d = self.dim()
        D = [r for _, r in self.rows]
        n = self.n
        vary = [j for j in range(n) if any(r[j] for r in D)]
        for size in range(d, len(vary) + 1):
            for B in itertools.combinations(vary, size):
                lb = [int(self.mins[i]) for i in B]
                lam, cst = {}, {}
                ok = True
                for j in range(n):
                    if j in B:
                        continue
                    got = None
                    for l in _solve(D, list(B), j, size == d, j in isref):
                        c = self.base[j] - sum(a * self.base[i] for a, i in zip(l, B)) \
                            + sum(a * m for a, m in zip(l, lb))
                        if c >= 0 and Fraction(c).denominator == 1:
                            got = (l, int(c))
                            break
                    if got is None:
                        ok = False
                        break
                    lam[j], cst[j] = got
                if ok:
                    return list(B), lam, cst, lb
        return None


LAMMAX = 4


def _solve(D, B, j, exact, pref):
    """lam >= 0 integers with D[k][j] = sum_i lam_i D[k][B_i] for every row k"""
    """(candidates, in order of preference)"""
    d = len(D)
    if exact and len(B) == d:
        M = [[D[k][i] for i in B] for k in range(d)]
        inv = _inv(M)
        if inv is None:
            return []
        col = [D[k][j] for k in range(d)]
        l = [sum(col[k] * inv[i][k] for k in range(d)) for i in range(len(B))]
        if any(x < 0 or x.denominator != 1 for x in l):
            return []
        return [[int(x) for x in l]]
    out = []
    for l in itertools.product(range(LAMMAX + 1), repeat=len(B)):
        if all(D[k][j] == sum(a * D[k][i] for a, i in zip(l, B)) for k in range(d)):
            key = (0 if (pref and any(l)) or (not pref and not any(l)) else 1, sum(l), l)
            out.append((key, list(l)))
    out.sort()
    return [l for _, l in out]


def _inv(M):
    d = len(M)
    A = [list(r) + [Fraction(int(i == j)) for j in range(d)] for i, r in enumerate(M)]
    for c in range(d):
        p = next((r for r in range(c, d) if A[r][c]), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        f = A[c][c]
        A[c] = [x / f for x in A[c]]
        for r in range(d):
            if r != c and A[r][c]:
                g = A[r][c]
                A[r] = [x - g * y for x, y in zip(A[r], A[c])]
    return [r[d:] for r in A]


class Fam:
    """one family per SHAPE (state, head, window shapes, tail states): the
    coordinates are the window blocks' exponents (left then right) and the
    refs (left, right: the sides with a tail); their values range over an
    affine hull, parametrized by a basis of coordinates"""

    def __init__(self, key):
        self.key = key
        self.q, self.h, self.sL, self.sR, self.tL, self.tR = key
        self.nb = sum(1 for x in self.sL + self.sR if x[0] == 'B')
        self.nc = self.nb + (self.tL is not None) + (self.tR is not None)
        self.hull = Hull(self.nc)
        self.version = 0
        self.fix()

    def fix(self):
        """the parametrization of the current hull"""
        H = self.hull
        if H.base is None:
            self.B, self.lam, self.cst, self.lb = [], {}, {}, []
            self.ex = ()
            self.n = 0
            return
        pr = H.param(isref=tuple(range(self.nb, self.nc)))
        if pr is None:
            raise Fail('no nonnegative parametrization')
        self._set(*pr)

    def _set(self, B, lam, cst, lb):
        self.B, self.lam, self.cst, self.lb = B, lam, cst, lb
        ex = []
        for j in range(self.nc):
            if j in B:
                k = B.index(j)
                ex.append((lb[k], ((k, 1),)))
            else:
                ex.append((cst[j], tuple((k, a) for k, a in enumerate(lam[j]) if a)))
        self.ex = tuple(ex)
        self.n = len(B)

    def match(self, exps):
        """tgt (aexps in z) with pattern(tgt) = exps, or None"""
        if self.hull.base is None:
            return None
        tgt = []
        for k, i in enumerate(self.B):
            e = exps[i]
            if e[0] < self.lb[k]:
                return None
            tgt.append((e[0] - self.lb[k], e[1]))
        for j in range(self.nc):
            if j in self.B:
                continue
            want = C.asubst(tgt, self.ex[j])
            if not aeq(want, exps[j]):
                return None
        return tgt

    def join(self, exps):
        """widen the hull by the affine set of exps; True if it changed"""
        e0 = [e[0] for e in exps]
        ks = sorted(set(k for e in exps for k, _ in e[1]))
        dirs = [[dict(e[1]).get(k, 0) for e in exps] for k in ks]
        if self.hull.add(e0, dirs):
            old = self.ex
            self.fix()
            if self.ex != old or True:
                self.version += 1
                return True
        return False

    def tstate(self, sd):
        return self.tL if sd == 'L' else self.tR

    def pattern(self):
        k = 0
        out = []
        for sh in (self.sL, self.sR):
            side = []
            for x in sh:
                if x[0] == 'L':
                    side.append(x)
                else:
                    side.append(('B', x[1], self.ex[k]))
                    k += 1
            out.append(side)
        return out

    def ref(self, sd):
        if self.tstate(sd) is None:
            return None
        i = self.nb
        if sd == 'R' and self.tL is not None:
            i += 1
        return self.ex[i]


class Explorer:
    def __init__(self, tab, pins):
        self.tab = tab
        self.tabw = {k: (None if k in pins else v) for k, v in tab.items()}
        self.nfa = NFA()
        self.fams = []
        self.fidx = {}
        self.trees = {}
        self.utrees = {}
        self.fleaves = {}
        self.failed = {}
        self.uses = collections.defaultdict(set)
        self.booting = False

    # -- folding --------------------------------------------------------
    def fold(self, sd, W, tail):
        """fold the outermost window items into the tail; learns the
        automaton.  Returns (window, tail spec (state, ref aexp) or None, folds)
        where folds are the (transition, exponent) pairs, nearest-first"""
        nfa = self.nfa
        W = list(W)
        folds = []
        cur = tail
        if cur is not None and (sd, cur[0]) in nfa.acc and not nfa.out(sd, cur[0]):
            cur = None              # an accepting state with no way on: the tail is empty
        while len(blocks_of(W)) > KEEP:
            last = W[-1]
            if last[0] == 'L':
                if cur is not None:
                    break
                bi = blocks_of(W)[-1]
                pred = W[bi]
                k = nfa.kind(sd, last[1], ())
                src = state_of_unit(pred[1])
                free = (sd, src, k, state_of_unit(()), (True, 0, 0)) in nfa.tidx
                pinned = [t for t in nfa.trans if t[0] == sd and t[1] == src and t[2] == k
                          and t[4][:2] == (False, 0)]
                if acoefs(pred[2]) or free:
                    rel = (True, 0, 0)
                else:
                    rel = (False, 0, pred[2][0])
                    if (sd, src, k, state_of_unit(()), rel) not in nfa.tidx:
                        if not self.booting:
                            break
                        if pinned:
                            # a second pinned length: the list may end anywhere
                            rel = (True, 0, 0)
                ti = nfa.learn(sd, src, k, rel)
                nfa.accept(sd, state_of_unit(()))
                folds.insert(0, (ti, (0, ())))
                cur = (src, pred[2])
                W = W[:-1]
                continue
            u, f = tuple(last[1]), last[2]
            if len(W) >= 2 and W[-2][0] == 'L':
                pre, nrm = tuple(W[-2][1]), 2
            else:
                pre, nrm = (), 1
            if len(W) - nrm - 1 < 0 or W[len(W) - nrm - 1][0] != 'B':
                break
            pred = W[len(W) - nrm - 1]
            k = nfa.kind(sd, pre, u)
            dst = None
            if cur is not None:
                s_old, r_old = cur
                if s_old[1] != u or dict(acoefs(f)) != dict(acoefs(r_old)):
                    break
                dl = s_old[2] + r_old[0] - f[0]
                dst = nfa.ensure_shift(sd, u, dl)
            src = state_of_unit(pred[1])
            rel = None
            for t in nfa.trans:
                if t[0] == sd and t[1] == src and t[2] == k and rel_ok(t[4], pred[2], f):
                    rel = t[4]
                    break
            if rel is None:
                rel = infer_rel(pred[2], f)
                if rel is None or not rel_ok(rel, pred[2], f):
                    break
                if not acoefs(pred[2]) and not acoefs(f) and (abs(rel[2]) > MAXD
                                                               or not self.booting):
                    break
            ti = nfa.learn(sd, src, k, rel, dst)
            if cur is None:
                nfa.accept(sd, state_of_unit(u))
            folds.insert(0, (ti, f))
            cur = (src, pred[2])
            W = W[:len(W) - nrm]
        return W, cur, folds

    def fam_of(self, q, h, L, R, tails, boot=False):
        """(fid, exps, changed?, folds) for a normalized end configuration;
        the family's hull is widened by exps.  tails: side -> None |
        (state, ref aexp)"""
        W, specs, folds = {}, {}, {}
        for sd, side in (('L', L), ('R', R)):
            units = set(k[2] for k in self.nfa.kinds if k[0] == sd and k[2])
            if not boot:
                # constant blocks back to literal (re-blocked by the side's
                # list units below): a separator stays a separator
                side = C.norm([x if x[0] == 'L' or acoefs(x[2]) else
                               ('L', C.rep(x[1], x[2][0])) for x in side])
            side = gen_segs(side, tails[sd] is None, units)
            W[sd], specs[sd], folds[sd] = self.fold(sd, side, tails[sd])
        exps = T.exps(W['L']) + T.exps(W['R'])
        for sd in ('L', 'R'):
            if specs[sd] is not None:
                exps.append(specs[sd][1])
        key = (q, h, T.shape(W['L']), T.shape(W['R']),
               None if specs['L'] is None else specs['L'][0],
               None if specs['R'] is None else specs['R'][0])
        if key not in self.fidx:
            if len(self.fams) >= MAXFAM:
                raise Fail('too many families')
            self.fidx[key] = len(self.fams)
            self.fams.append(Fam(key))
        fid = self.fidx[key]
        F = self.fams[fid]
        ch = False
        if F.match(exps) is None:
            ch = F.join(exps)
            if F.match(exps) is None:
                raise Fail('join does not cover its target')
        return fid, exps, ch, folds

    # -- exploration ------------------------------------------------------
    def data_pass(self, boot, nleaves):
        """follow the REAL run leaf by leaf from the boot (the same cuts, folds
        and unfolds as the exploration, the tails concrete), joining every
        value vector into its family's hull"""
        q, L, h, R, tails, conc = boot
        self.booting = True
        f0, ex0, _, folds0 = self.fam_of(q, h, L, R, tails, boot=True)
        self.booting = False
        nfa = self.nfa
        fid, vals = f0, [e[0] for e in ex0]
        ctail = {sd: list(conc[sd]) for sd in ('L', 'R')}
        self.booting = True
        try:
            for _ in range(nleaves):
                F = self.fams[fid]
                # the window, concrete
                k = 0
                ext = {}
                for sd, sh in (('L', F.sL), ('R', F.sR)):
                    segs = []
                    for x in sh:
                        if x[0] == 'L':
                            segs.append(x)
                        else:
                            segs.append(('B', x[1], (vals[k], ())))
                            k += 1
                    ext[sd] = segs
                st, end, ref = {}, {}, {}
                ri = F.nb
                for sd in ('L', 'R'):
                    s_ = F.tstate(sd)
                    if s_ is None:
                        st[sd], end[sd] = None, True
                    else:
                        st[sd], end[sd], ref[sd] = s_, False, vals[ri]
                        ri += 1
                while True:
                    try:
                        lf = leaf_run(self.tabw, F.q, F.h, ext['L'], ext['R'], end['L'],
                                      end['R'], 0, 1)
                        break
                    except Req as rq:
                        if rq.kind != 'unf':
                            raise Fail('data pass: %s' % rq.kind)
                        sd = rq.k
                        if not ctail[sd]:
                            end[sd] = True
                            continue
                        ti, e = ctail[sd].pop(0)
                        ext[sd] = ext[sd] + item_segs(nfa, nfa.trans[ti][2], (e, ()))
                        st[sd], ref[sd] = nfa.trans[ti][3], e
                Ln = fnorm(lf['endL'])
                Rn = fnorm(lf['endR'])
                if end['L']:
                    Ln = C.nstrip(Ln)
                if end['R']:
                    Rn = C.nstrip(Rn)
                tails = {sd: (None if end[sd] else (st[sd], (ref[sd], ()))) for sd in ('L', 'R')}
                if any(end[sd] and ctail[sd] for sd in ('L', 'R')):
                    raise Fail('data pass: ended with a tail')
                fid, exps, _, folds = self.fam_of(lf['q1'], lf['h1'], Ln, Rn, tails)
                vals = [e[0] for e in exps]
                for sd in ('L', 'R'):
                    ctail[sd] = [(ti, e[0]) for ti, e in folds[sd]] + ctail[sd]
        finally:
            self.booting = False
        self.nfa.touched.clear()

    def explore(self, boot):
        q, L, h, R, tails, conc = boot
        f0, ex0, _, folds0 = self.fam_of(q, h, L, R, tails, boot=True)
        self.boot = (f0, ex0, folds0, conc)
        todo = [f0]
        rounds = 0
        while todo:
            rounds += 1
            if rounds > MAXROUNDS:
                raise Fail('exploration does not settle')
            fid = todo.pop(0)
            if fid in todo:
                continue
            if VERBOSE and rounds % 50 == 0:
                print('  round %d: %d families, %d todo, %d transitions, %d failed' % (
                    rounds, len(self.fams), len(todo), len(self.nfa.trans), len(self.failed)),
                      file=sys.stderr, flush=True)
            F = self.fams[fid]
            v0 = F.version
            try:
                self.explore_fam(fid, todo)
                self.failed.pop(fid, None)
            except Fail as e:
                self.failed[fid] = str(e)
                self.trees.pop(fid, None)
                self.fleaves.pop(fid, None)
            if F.version != v0 and fid not in todo:
                todo.append(fid)
            if self.nfa.touched:
                for st in list(self.nfa.touched):
                    for f2 in self.uses.get(st, ()):
                        self.trees.pop(f2, None)
                        self.fleaves.pop(f2, None)
                        if f2 not in todo:
                            todo.append(f2)
                self.nfa.touched.clear()
        # the families the boot reaches
        reach, stack = set(), [f0]
        while stack:
            f = stack.pop()
            if f in reach:
                continue
            reach.add(f)
            if f in self.failed:
                raise Fail('%s (family %d)' % (self.failed[f], f))
            if f not in self.fleaves:
                raise Fail('unexplored family %d' % f)
            for lf in self.fleaves[f]:
                stack.append(lf['g'])
        self.reach = reach

    def explore_fam(self, fid, todo):
        self.mins = self.nfa.mins()
        F = self.fams[fid]
        nfa = self.nfa
        nodes, unodes, leaves = [], [], []
        pat = F.pattern()
        used = set()

        class Up(Exception):
            def __init__(self, rq):
                self.rq = rq

        def run_unf(R, paths, na, p):
            """a leaf, or an unfold node, below region R.  paths: side ->
            list of (transition, exponent) or 'end' entries"""
            if len(leaves) > MAXLEAF:
                raise Fail('too many leaves')
            sub = C.rsub(R)
            ext, end, st = {}, {}, {}
            for sd, pt in (('L', pat[0]), ('R', pat[1])):
                segs = [C.seg_subst(sub, x) for x in pt]
                r = F.ref(sd)
                if r is None:
                    end[sd] = True
                    st[sd] = None
                else:
                    r = C.asubst(sub, r)
                    s = F.tstate(sd)
                    end[sd] = False
                    for ent in paths[sd]:
                        if ent == 'end':
                            end[sd] = True
                            break
                        ti, u = ent
                        segs = segs + item_segs(nfa, nfa.trans[ti][2], u)
                        s, r = nfa.trans[ti][3], u
                    st[sd] = (s, r)
                ext[sd] = segs
            mins = self.mins
            for sd in ('L', 'R'):
                if st[sd] is None or end[sd]:
                    continue
                s_, r_ = st[sd]
                used.add((sd, s_))
                mm = mins.get((sd, s_), 0)
                if mm == float('inf'):
                    raise Fail('state with no valid tail')
                if r_[0] < mm:
                    cs = acoefs(r_)
                    if not cs:
                        me = len(unodes)
                        unodes.append(('void', sd))
                        return me
                    if len(cs) == 1:
                        k, m_ = cs[0]
                        raise Up(Req('uge', k, -(-(mm - r_[0]) // m_)))
            while True:
                try:
                    lf = leaf_run(self.tabw, F.q, F.h, ext['L'], ext['R'], end['L'], end['R'],
                                  na, p)
                    break
                except Req as rq:
                    if rq.kind == 'na':
                        na = rq.n
                        continue
                    if rq.kind == 'unf':
                        sd = rq.k
                        if len(paths[sd]) >= MAXUNF:
                            raise Fail('unfold depth')
                        s, r = st[sd]
                        used.add((sd, s))
                        me = len(unodes)
                        unodes.append(None)
                        kids = []
                        if (sd, s) in nfa.acc:
                            p2 = dict(paths)
                            p2[sd] = paths[sd] + ['end']
                            kids.append(run_unf(R, p2, na, p))
                        for ti in nfa.out(sd, s):
                            u = rel_apply(nfa.trans[ti][4], r)
                            if u != 'void' and not (isinstance(u[0], str)) and not acoefs(u) \
                                    and u[0] < self.mins.get((sd, nfa.trans[ti][3]), 0):
                                u = 'void'
                            if u == 'void':
                                kids.append(None)
                                continue
                            if isinstance(u, tuple) and u and isinstance(u[0], str):
                                raise Up(Req('u' + u[0], u[1], u[2]))
                            p2 = dict(paths)
                            p2[sd] = paths[sd] + [(ti, u)]
                            kids.append(run_unf(R, p2, na, p))
                        unodes[me] = ('unf', sd, (sd, s) in nfa.acc, kids)
                        return me
                    raise Up(rq)
            Ln = fnorm(lf['endL'])
            Rn = fnorm(lf['endR'])
            if end['L']:
                Ln = C.nstrip(Ln)
            if end['R']:
                Rn = C.nstrip(Rn)
            tails = {sd: (None if end[sd] else st[sd]) for sd in ('L', 'R')}
            g, ex, low, folds = self.fam_of(lf['q1'], lf['h1'], Ln, Rn, tails)
            lf.update(reg=list(R), g=g, ex=ex, unf=paths, folds=folds, end=dict(end))
            me = len(unodes)
            unodes.append(('uleaf', len(leaves)))
            leaves.append(lf)
            if low or g not in self.fleaves:
                if g not in todo:
                    todo.append(g)
            return me

        def build(R, na, p):
            while True:
                try:
                    u0, l0 = len(unodes), len(leaves)
                    ui = run_unf(R, {'L': [], 'R': []}, na, p)
                    me = len(nodes)
                    nodes.append(('leaf', ui))
                    return me
                except Up as up:
                    rq = up.rq
                    # discard what the failed attempt built
                    del unodes[u0:]
                    del leaves[l0:]
                    k = rq.k
                    M, c = R[k]
                    me = len(nodes)
                    nodes.append(None)
                    if rq.kind in ('ge', 'uge'):
                        n = rq.n
                        kids = []
                        for v in range(n):
                            R2 = list(R)
                            R2[k] = (0, c + M * v)
                            kids.append(build(R2, 0, 1))
                        R2 = list(R)
                        R2[k] = (M, c + M * n)
                        kids.append(build(R2, na, p))
                        nodes[me] = ('split', k, n, 1, kids)
                    elif rq.kind in ('mod', 'pow', 'umod'):
                        pp = rq.n
                        kids = []
                        for s in range(pp):
                            R2 = list(R)
                            R2[k] = (M * pp, c + M * s)
                            kids.append(build(R2, na, p if rq.kind == 'umod' else pp))
                        nodes[me] = ('split', k, 0, pp, kids)
                    else:
                        raise Fail('request %s' % rq.kind)
                    return me

        nlv0 = len(leaves)
        build([(1, 0)] * F.n, 0, 1)
        for st in used:
            self.uses[st].add(fid)
        self.trees[fid] = nodes
        self.utrees[fid] = unodes
        self.fleaves[fid] = leaves


# ---------------------------------------------------------------- boot ----

def run_rec(tab, n):
    """the configuration at the last record step (the head on a new cell)
    at or before step n: (q, L, h, R, t)"""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    last = None
    for t in range(n):
        h = tape.get(pos, 0)
        tr = tab[(q, h)]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
        if pos < lo or pos > hi:
            lo, hi = min(lo, pos), max(hi, pos)
            last = (t + 1, q, pos, lo, hi)
    t, q, pos, lo, hi = last
    return T.run_conc(tab, t)[:4] + (t,)


def boot_of(X, tab, t0):
    """the concrete tape after t0 steps as (q, L, h, R, tails, concrete tails):
    the window keeps KEEP blocks a side, the rest are tail items whose
    relations are read off the concrete lengths (the list ratio)"""
    r = run_rec(X.tabw, t0)
    if r is None:
        raise Fail('halts')
    q, L, h, R, t0 = r
    X.t0 = t0
    nfa = X.nfa
    X.booting = True
    out, tails, conc = {}, {}, {}
    rs = []
    for side in (L, R):
        es = [x[2][0] for x in gen_side(side) if x[0] == 'B']
        for a, b in zip(es, es[1:]):
            lo, hi = min(a, b), max(a, b)
            if lo >= 8:
                rs.append(round(hi / lo))
    RATIO[0] = max(1, min(BOOT_AMAX, collections.Counter(rs).most_common(1)[0][0])) if rs else 2
    for sd, side in (('L', L), ('R', R)):
        segs = gen_side(side)
        W, cur, folds = X.fold(sd, segs, None)
        out[sd] = W
        tails[sd] = cur
        conc[sd] = [(ti, e[0]) for ti, e in folds]
    X.booting = False
    return q, out['L'], h, out['R'], tails, conc


NDATA = 3000


def explore_row(spec, t0, mir=False):
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        raise Fail('halts')
    pins = set(k for k in tab if k not in r2[4])
    X = Explorer(tab, pins)
    global _lastX
    _lastX = X
    boot = boot_of(X, tab, t0)
    X.data_pass(boot, NDATA)
    X.explore(boot)
    return X, pins, boot
