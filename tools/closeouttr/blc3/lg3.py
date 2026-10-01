#!/usr/bin/env python3
"""BLC3: block-list rows through ListGlueTr with a JOINT tail language
(UNTRUSTED finder; SCOPING_INSTR.md §7.4.BLC3).

BLC2's explorer (lg_batch.Explorer) learned one automaton per side from a
short data pass.  The two sides of a block list are one counter, and the
learned per-side automata let the exploration build lists the machine never
builds.  Here the tail language is ONE forward automaton F over the whole
list, read from the list's head end b_0 to its far end:

  * a list b_0, b_1, ..., b_k has digits d_i = b_i - a * b_(i+1) (a the
    ratio); F reads d_0, d_1, ..., d_(k-1) and then the far end (the last
    block pinned to a constant by an end item of exponent 0);
  * the LEFT tail (items b_(i-1), ..., b_0 nearest-first, b_0 last) is read
    by F itself, from b_0: a fold prepends the item nearest the window, so
    the fold direction is F's forward direction (deterministic);
  * the RIGHT tail (items b_j, ..., b_k, END nearest-first) is read by the
    determinised REVERSE of F from the far end: a state is the set of F's
    states from which the rest of the list is accepted.

So a family's two tail states are both measured from ONE reading of the
list, and a family is exact: Pre_F(q_L) x window x Suf(R) is a subset of
the language when the window's digits lead from q_L into R.

The window is parsed in TAPE order (left side, head cell, right side) into
list elements (runs of the unit) and separators, so an element split by the
head keeps its full exponent; its neighbour relations are keyed (wrel), and
constant elements up to SMALL cells stay literal, so the far end never
generalises.  Everything else (hulls, the dispatch trees, unfold nodes, the
liveness search, the replica, the renderer) is lg_batch's.
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import lg_batch as G                              # noqa: E402
import ti_batch as T                              # noqa: E402
import ti_coq as C                                # noqa: E402

Fail, Req, NonCanon = T.Fail, T.Req, G.NonCanon
aeq, acoefs = G.aeq, G.acoefs

SMALL = int(os.environ.get('LG3_SMALL', '7'))
KEEP = int(os.environ.get('LG3_KEEP', '1'))
VERBOSE = bool(os.environ.get('LG_VERBOSE'))

# ------------------------------------------------------------ language ----


class Lang:
    """a forward automaton over a list's SYMBOLS (see the module doc).  The
    list b_0, ..., b_k reads as symbols x_i = (w_i, d_i): w_i the separator
    word between b_i and b_(i+1) (tape order), d_i = b_i - a b_(i+1).

    fwd[(q, x)] = q2   transitions;
    end[q] = [(x, bk)] the list may end from q with a last symbol x and a
                       last block of bk cells (pinned by an END item);
    q0 the state before x_0; shift: b_0 in a LEFT tail is b_0 + shift of the
    list F describes; lstart / lfwd: the LEFT tails' own sub-automaton
    (b_0's symbols, unshifted, with the state after it; the rest)."""

    def __init__(self, a, unit, fwd, end, q0, shift=0, lfwd=None, lstart=None, seps=None):
        self.a, self.unit = a, tuple(unit)
        self.fwd, self.end, self.q0, self.shift = dict(fwd), dict(end), q0, shift
        self.lfwd = dict(fwd) if lfwd is None else dict(lfwd)
        self.lstart = [(x, q2) for (q, x), q2 in self.fwd.items() if q == q0] \
            if lstart is None else list(lstart)
        ws = set(x[0] for (_, x) in self.fwd) | set(x[0] for lst in self.end.values()
                                                   for x, _ in lst)
        ws |= set(x[0] for (_, x) in self.lfwd) | set(x[0] for x, _ in self.lstart)
        self.seps = sorted(set(seps or ()) | ws, key=lambda w: (-len(w), w))

    def automaton(self):
        """the lg_batch.NFA of both sides: transitions (side, src = the
        state nearer the window, kind, dst, rel), and the fold map
        fold[(side, q_far, kind, rel)] = transition index"""
        nfa = G.NFA()
        u = self.unit
        kL = {w: nfa.kind('L', tuple(reversed(w)), u) for w in self.seps}
        kR = {w: nfa.kind('R', tuple(w), u) for w in self.seps}
        kE = nfa.kind('R', (0,), u)
        fold = {}

        def add(sd, q_near, k, q_far, rel):
            key = (sd, q_near, k, q_far, rel)
            if key not in nfa.tidx:
                nfa.tidx[key] = len(nfa.trans)
                nfa.trans.append(key)
            ti = nfa.tidx[key]
            old = fold.get((sd, q_far, k, rel))
            if old is not None and old != ti:
                raise Fail('lang: fold not deterministic on side %s' % sd)
            fold[(sd, q_far, k, rel)] = ti
        a = self.a
        # LEFT: F forward from b_0; 'L0' is the far end (b_0 not read yet)
        byq = collections.defaultdict(list)
        for (q, x), q2 in self.lfwd.items():
            byq[q].append((x, q2))
        seen, todo = set(), []
        for (w, d), q2 in self.lstart:
            add('L', ('F', q2), kL[w], 'L0', (True, a, d + self.shift))
            todo.append(q2)
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.add(q)
            for (w, d), q2 in byq[q]:
                add('L', ('F', q2), kL[w], ('F', q), (True, a, d))
                todo.append(q2)
        nfa.acc.add(('L', 'L0'))
        # RIGHT: the determinised reverse of F from the far end
        ends = []                      # (q, x, bk)
        for q, lst in self.end.items():
            for x, bk in lst:
                ends.append((q, x, bk))
        # the far end: an END item (exponent 0) pins b_k; state = frozenset
        # of ('Z', q, x, bk): "the last symbol x from q, b_k = bk"
        start = frozenset([('FIN',)])
        rstates = {}
        todo = []
        bybk = collections.defaultdict(set)
        for q, x, bk in ends:
            bybk[bk].add(('Z', q, x, bk))
        for bk, zs in bybk.items():
            s = frozenset(zs)
            add('R', ('R', s), kE, ('R', start), (False, 0, bk))
            todo.append(s)
        pred = collections.defaultdict(set)      # (q2, x) -> {q}
        for (q, x), q2 in self.fwd.items():
            pred[(q2, x)].add(q)
        syms = sorted(set(x for (_, x) in self.fwd) | set(x for _, x, _ in ends))
        while todo:
            s = todo.pop()
            if s in rstates:
                continue
            rstates[s] = True
            for x in syms:
                prev = set()
                for z in s:
                    if z[0] == 'Z':
                        if z[2] == x:
                            prev.add(z[1])
                    else:
                        prev |= pred.get((z, x), set())
                if not prev:
                    continue
                p = frozenset(prev)
                add('R', ('R', p), kR[x[0]], ('R', s), (False, a, x[1]))
                todo.append(p)
        nfa.acc.add(('R', ('R', start)))
        self.nfa, self.foldmap, self.kL, self.kR, self.kE = nfa, fold, kL, kR, kE
        return nfa


# ------------------------------------------------------------- parsing ----

def aesum(es):
    acc = (0, ())
    for e in es:
        acc = C.aadd(acc, e)
    return acc


def tape_tokens(L, h, R):
    """tape-order tokens of a window: ('c', sym, side) cells and
    ('b', unit, aexp, side) blocks; the head cell is ('c', h, 'H')"""
    toks = []
    for x in reversed(L):
        if x[0] == 'L':
            for s in reversed(x[1]):
                toks.append(('c', s, 'L'))
        else:
            toks.append(('b', tuple(reversed(x[1])), x[2], 'L'))
    toks.append(('c', h, 'H'))
    for x in R:
        if x[0] == 'L':
            for s in x[1]:
                toks.append(('c', s, 'R'))
        else:
            toks.append(('b', tuple(x[1]), x[2], 'R'))
    return toks


def elements(toks, unit):
    """[(kind, i0, i1, exp)] over the tokens: kind 'E' a maximal run of the
    (one-cell) unit, exp its length (affine); kind 'G' anything else (a gap:
    the cells between two runs)"""
    (u,) = unit
    out = []
    i = 0
    while i < len(toks):
        t = toks[i]
        isu = (t[0] == 'c' and t[1] == u) or (t[0] == 'b' and tuple(t[1]) == (u,))
        j = i
        if isu:
            es = []
            while j < len(toks) and ((toks[j][0] == 'c' and toks[j][1] == u) or
                                     (toks[j][0] == 'b' and tuple(toks[j][1]) == (u,))):
                es.append((1, ()) if toks[j][0] == 'c' else toks[j][2])
                j += 1
            out.append(('E', i, j, aesum(es)))
        else:
            while j < len(toks) and not ((toks[j][0] == 'c' and toks[j][1] == u) or
                                         (toks[j][0] == 'b' and tuple(toks[j][1]) == (u,))):
                j += 1
            out.append(('G', i, j, tuple(toks[k] for k in range(i, j))))
        i = j
    return out


def gap_word(g, seps):
    """the separator word a gap is (cells only), or None"""
    cells = g[3]
    if any(t[0] != 'c' for t in cells):
        return None
    w = tuple(t[1] for t in cells)
    return w if w in seps else None


def parse(toks, unit, seps):
    """elements() with the separators merged: a gap, a literal run of the
    unit and a gap that together spell a separator word are one gap (the
    word 010 between two runs of 1, say).  The finder's data and its
    exploration parse by this one function."""
    el = elements(toks, unit)
    sepset = set(seps)
    maxw = max([len(w) for w in seps] + [0])
    out = []
    i = 0
    while i < len(el):
        x = el[i]
        if x[0] == 'G' and out and out[-1][0] == 'E' and i + 2 < len(el):
            # try the longest merge G E G (E literal) ... that spells a word
            best = None
            j = i
            cells = list(x[3])
            while j + 2 < len(el) and el[j + 1][0] == 'E' and el[j + 2][0] == 'G':
                mid = toks[el[j + 1][1]:el[j + 1][2]]
                if any(t[0] != 'c' for t in mid):
                    break
                cells = cells + list(mid) + list(el[j + 2][3])
                if len(cells) > maxw:
                    break
                if tuple(t[1] for t in cells) in sepset and j + 3 < len(el) and el[j + 3][0] == 'E':
                    best = (j + 2, tuple(cells))
                j += 2
            if best is not None:
                j2, cells = best
                out.append(('G', x[1], el[j2][2], cells))
                i = j2 + 1
                continue
        out.append(x)
        i += 1
    return out


def rel_of(up, a, p, e):
    """the digit d with e = a p + d (up) / p = a e + d (down), or None"""
    if up:
        diff = C.aadd(e, (0, ())), C.ascale(a, p)
    else:
        diff = p, C.ascale(a, e)
    x, y = diff
    # x - y constant?
    dx, dy = dict(acoefs(x)), dict(acoefs(y))
    if dx != dy:
        return None
    return x[0] - y[0]


from fractions import Fraction                      # noqa: E402
import itertools                                    # noqa: E402
import math                                         # noqa: E402


class LHull(G.Hull):
    """lg_batch.Hull plus, per coordinate, the gcd of every difference of
    joined values (and of every direction joined): the family is a LATTICE
    lb + g x, not the whole affine hull.  A block that is always even at an
    anchor stays even (Karr's hull alone forgets it, and the exploration
    then builds the odd lengths the machine never builds)"""

    def __init__(self, n):
        super().__init__(n)
        self.g = [0] * n

    def add(self, e0, ks):
        base = self.base
        ch = super().add(e0, ks)
        b = self.base if base is None else base
        for i in range(self.n):
            g = self.g[i]
            g2 = math.gcd(g, abs(int(e0[i] - b[i])))
            for k in ks:
                g2 = math.gcd(g2, abs(int(k[i])))
            if g2 != g:
                self.g[i] = g2
                ch = True
        return ch

    def param(self, isref=()):
        d = self.dim()
        D = [r for _, r in self.rows]
        n = self.n
        vary = [j for j in range(n) if any(r[j] for r in D)]
        order = [j for j in vary if j not in isref] + [j for j in vary if j in isref]
        for B in itertools.combinations(order, d):
            M = [[D[k][i] for i in B] for k in range(d)]
            inv = G._inv(M) if d else []
            if d and inv is None:
                continue
            lb = [int(self.mins[i]) for i in B]
            gs = [self.g[i] or 1 for i in B]
            lam, cst = {}, {}
            ok = True
            for j in range(n):
                if j in B:
                    continue
                col = [D[k][j] for k in range(d)]
                l = [sum(col[k] * inv[i][k] for k in range(d)) for i in range(d)]
                c = self.base[j] + sum(a * (m - self.base[i]) for a, m, i in zip(l, lb, B))
                co = [a * g for a, g in zip(l, gs)]
                if c < 0 or Fraction(c).denominator != 1 or \
                        any(x < 0 or Fraction(x).denominator != 1 for x in co):
                    ok = False
                    break
                lam[j], cst[j] = [int(x) for x in co], int(c)
            if ok:
                return list(B), lam, cst, lb, gs
        return None


class LFam(G.Fam):
    def __init__(self, key):
        self.key = key
        self.q, self.h, self.sL, self.sR, self.tL, self.tR, self.wrel = key
        self.nb = sum(1 for x in self.sL + self.sR if x[0] == 'B')
        self.nc = self.nb + (self.tL is not None) + (self.tR is not None)
        self.hull = LHull(self.nc)
        self.version = 0
        self.fix()

    def fix(self):
        H = self.hull
        if H.base is None:
            self.B, self.lam, self.cst, self.lb, self.gs = [], {}, {}, [], []
            self.ex = ()
            self.n = 0
            return
        pr = H.param(isref=tuple(range(self.nb, self.nc)))
        if pr is None:
            raise Fail('no nonnegative parametrization')
        B, lam, cst, lb, gs = pr
        self.B, self.lam, self.cst, self.lb, self.gs = B, lam, cst, lb, gs
        ex = []
        for j in range(self.nc):
            if j in B:
                k = B.index(j)
                ex.append((lb[k], ((k, gs[k]),)))
            else:
                ex.append((cst[j], tuple((k, a) for k, a in enumerate(lam[j]) if a)))
        self.ex = tuple(ex)
        self.n = len(B)

    def match(self, exps):
        if self.hull.base is None:
            return None
        tgt = []
        for k, i in enumerate(self.B):
            e = exps[i]
            g = self.gs[k]
            if e[0] < self.lb[k] or (e[0] - self.lb[k]) % g or any(a % g for _, a in e[1]):
                return None
            tgt.append(((e[0] - self.lb[k]) // g, tuple((v, a // g) for v, a in e[1])))
        for j in range(self.nc):
            if j in self.B:
                continue
            want = C.asubst(tgt, self.ex[j])
            if not aeq(want, exps[j]):
                return None
        return tgt


def cprefix_lit(segs, i):
    """the literal prefix of a side, stopping at ANY block (constant blocks
    too: a leaf then crosses at most one element of a list, symbolic or
    constant, so a canonical unfold never chases a walk along a row of
    constant elements)"""
    pre = ()
    while i < len(segs) and segs[i][0] == 'L':
        pre += tuple(segs[i][1])
        i += 1
    return pre, i


def cprefix_one(segs, i):
    """the literal prefix plus at most one leading constant block (the one
    the leaf starts by crossing) and the literals after it"""
    pre, i = cprefix_lit(segs, i)
    if i < len(segs) and segs[i][0] == 'B' and not segs[i][2][1]:
        pre += C.rep(segs[i][1], segs[i][2][0])
        p2, i = cprefix_lit(segs, i + 1)
        pre += p2
    return pre, i


def leaf_run3(tabw, q, h, Lz, Rz, endL, endR, na, p):
    """lg_batch.leaf_run, except that a constant block stops the leaf like a
    symbolic one (the start block, if constant, is crossed literally)"""
    old = T.cprefix
    try:
        T.cprefix = _cprefix_dispatch
        _cprefix_dispatch.first = True
        return _leaf_run_orig(tabw, q, h, Lz, Rz, endL, endR, na, p)
    finally:
        T.cprefix = old


def _cprefix_dispatch(segs, i):
    # lg_batch.leaf_run calls cprefix for: the direction side at 0 (crossing
    # a constant start block is allowed), then the direction side after the
    # start block, then the other side at 0
    if _cprefix_dispatch.first:
        _cprefix_dispatch.first = False
        return cprefix_one(segs, i)
    return cprefix_lit(segs, i)


_leaf_run_orig = G.leaf_run
if os.environ.get('LG3_CSTOP', '1') == '1':
    G.leaf_run = leaf_run3


def nfa_maxs(nfa):
    """per (side, state): an UPPER bound on the ref of any valid tail, where
    one exists (ListGlue2Tr's [lc_maxs]).  A state is bounded when it is not
    accepting (the empty tail allows any ref) and each of its transitions
    either pins the ref (down, a = 0) or relates it to a bounded state by
    a >= 1 (a least fixpoint: no cycle is bounded)."""
    trs = collections.defaultdict(list)
    states = set()
    for (sd, src, k, dst, rel) in nfa.trans:
        trs[(sd, src)].append(((sd, dst), rel))
        states.add((sd, src))
        states.add((sd, dst))
    m = {}
    while True:
        ch = False
        for st in states:
            if st in m or st in nfa.acc:
                continue
            best = -1
            ok = True
            for dst, (up, a, d) in trs[st]:
                if not up and a == 0:
                    b = d
                elif a == 0 or dst not in m:
                    ok = False
                    break
                elif up:
                    b = (m[dst] + max(-d, 0)) // a      # ListGlue2Tr.rubound
                else:
                    b = a * m[dst] + max(d, 0)
                best = max(best, b)
            if ok and trs[st]:
                m[st] = max(best, 0)
                ch = True
        if not ch:
            break
    return m


class X3(G.Explorer):
    """lg_batch.Explorer with a fixed joint language and the tape-order
    canonical fold"""

    def __init__(self, tab, pins, lang):
        super().__init__(tab, pins)
        self.lang = lang
        self.nfa = lang.automaton()
        self.foldmap = lang.foldmap

    def explore_fam(self, fid, todo):
        self.mins = self.nfa.mins()
        self.maxs = nfa_maxs(self.nfa)
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
            if len(leaves) > G.MAXLEAF:
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
                        segs = segs + G.item_segs(nfa, nfa.trans[ti][2], u)
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
                mx = self.maxs.get((sd, s_))
                if mx is not None:
                    if r_[0] > mx:
                        me = len(unodes)
                        unodes.append(('void', sd))
                        return me
                    cs = acoefs(r_)
                    if len(cs) == 1:
                        k, m_ = cs[0]
                        raise Up(Req('uge', k, (mx - r_[0]) // m_ + 1))
                    if cs:
                        raise Fail('max on a multi-variable ref')
            def unfold(sd):
                if len(paths[sd]) >= G.MAXUNF:
                    raise Fail('unfold depth')
                s, r = st[sd]
                used.add((sd, s))
                me = len(unodes)
                unodes.append(None)
                kids = []
                endk = None
                if (sd, s) in nfa.acc:
                    p2 = dict(paths)
                    p2[sd] = paths[sd] + ['end']
                    endk = run_unf(R, p2, na, p)
                for ti in nfa.out(sd, s):
                    u = G.rel_apply(nfa.trans[ti][4], r)
                    mxd = self.maxs.get((sd, nfa.trans[ti][3]))
                    if u != 'void' and not (isinstance(u[0], str)) and \
                            ((not acoefs(u) and u[0] < self.mins.get((sd, nfa.trans[ti][3]), 0))
                             or (mxd is not None and u[0] > mxd)):
                        # the item is below its state's least ref: a void node
                        vi = len(unodes)
                        unodes.append(('void', sd))
                        kids.append((ti, u, vi))
                        continue
                    if u == 'void':
                        kids.append((ti, None, None))
                        continue
                    if isinstance(u, tuple) and u and isinstance(u[0], str):
                        raise Up(Req('u' + u[0], u[1], u[2]))
                    p2 = dict(paths)
                    p2[sd] = paths[sd] + [(ti, u)]
                    kids.append((ti, u, run_unf(R, p2, na, p)))
                unodes[me] = ('unf', sd, endk, kids)
                return me

            while True:
                try:
                    lf = G.leaf_run(self.tabw, F.q, F.h, ext['L'], ext['R'], end['L'], end['R'],
                                  na, p)
                    break
                except Req as rq:
                    if rq.kind == 'na':
                        na = rq.n
                        continue
                    if rq.kind == 'unf':
                        return unfold(rq.k)
                    raise Up(rq)
            Ln = G.fnorm(lf['endL'])
            Rn = G.fnorm(lf['endR'])
            if end['L']:
                Ln = C.nstrip(Ln)
            if end['R']:
                Rn = C.nstrip(Rn)
            tails = {sd: (None if end[sd] else st[sd]) for sd in ('L', 'R')}
            try:
                g, ex, low, folds = self.fam_of(lf['q1'], lf['h1'], Ln, Rn, tails)
            except NonCanon as nc:
                return unfold(nc.sd)
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

    def fold(self, sd, W, tail):          # not used (fam_of folds)
        raise Fail('X3.fold')

    def fam_of(self, q, h, L, R, tails, boot=False):
        lang = self.lang
        toks = tape_tokens(L, h, R)
        el = parse(toks, lang.unit, lang.seps)
        hidx = next(i for i, t in enumerate(toks) if t[-1] == 'H')
        # element distance from the head
        Es = [k for k, x in enumerate(el) if x[0] == 'E']

        def dist(k):
            x = el[k]
            if x[1] <= hidx < x[2]:
                return 0
            if x[2] <= hidx:
                return sum(1 for k2 in Es if k2 >= k and el[k2][2] <= hidx)
            return sum(1 for k2 in Es if k2 <= k and el[k2][1] > hidx)
        # canonical tails: the outermost element must be the tail's ref
        lo, hi = 0, len(el)             # the window: el[lo:hi]
        folds = {'L': [], 'R': []}
        specs = {}
        for sd in ('L', 'R'):
            tl = tails[sd]
            if tl is None:
                continue
            k = 0 if sd == 'L' else len(el) - 1
            if not el or el[k][0] != 'E' or not aeq(el[k][3], tl[1]):
                raise NonCanon(sd)
        a = lang.a
        # LEFT: fold from the outer end
        cur = tails['L'][0] if tails['L'] is not None else None
        curref = tails['L'][1] if tails['L'] is not None else None
        fl = []
        if cur is None:
            if el and el[0][0] == 'G':
                pass                # junk at the far end: no tail
            else:
                cur = 'L0'
        k = 0
        while cur is not None and k + 2 < len(el) and el[k][0] == 'E' and \
                el[k + 1][0] == 'G' and gap_word(el[k + 1], lang.seps) is not None and \
                el[k + 2][0] == 'E' and dist(k) > KEEP and \
                all(toks[i][-1] == 'L' for i in range(el[k][1], el[k + 1][2])):
            d = rel_of(True, a, el[k + 2][3], el[k][3])
            if d is None:
                break
            w = gap_word(el[k + 1], lang.seps)
            ti = self.foldmap.get(('L', cur, lang.kL[w], (True, a, d)))
            if ti is None:
                break
            fl.insert(0, (ti, el[k][3]))
            cur = self.nfa.trans[ti][1]
            k += 2
        lo = k
        if cur is not None and (fl or tails['L'] is not None):
            specs['L'] = (cur, el[lo][3])
            folds['L'] = fl
        else:
            specs['L'] = None
        # RIGHT
        cur = tails['R'][0] if tails['R'] is not None else None
        fr = []
        k = len(el) - 1
        start = ('R', frozenset([('FIN',)]))
        if cur is None:
            if el and el[-1][0] == 'E' and not acoefs(el[-1][3]) and dist(k) > KEEP \
                    and all(toks[i][-1] == 'R' for i in range(el[k][1], el[k][2])):
                ti = self.foldmap.get(('R', start, lang.kE, (False, 0, el[-1][3][0])))
                if ti is not None:
                    fr.insert(0, (ti, (0, ())))
                    cur = self.nfa.trans[ti][1]
        while cur is not None and k - 2 >= lo and el[k][0] == 'E' and \
                el[k - 1][0] == 'G' and gap_word(el[k - 1], lang.seps) is not None and \
                el[k - 2][0] == 'E' and dist(k) > KEEP and \
                all(toks[i][-1] == 'R' for i in range(el[k - 1][1], el[k][2])):
            d = rel_of(False, a, el[k - 2][3], el[k][3])
            if d is None:
                break
            w = gap_word(el[k - 1], lang.seps)
            ti = self.foldmap.get(('R', cur, lang.kR[w], (False, a, d)))
            if ti is None:
                break
            fr.insert(0, (ti, el[k][3]))
            cur = self.nfa.trans[ti][1]
            k -= 2
        hi = k + 1
        if cur is not None and (fr or tails['R'] is not None):
            if hi - 1 < lo or el[hi - 1][0] != 'E':
                raise Fail('right tail without a ref')
            specs['R'] = (cur, el[hi - 1][3])
            folds['R'] = fr
        else:
            specs['R'] = None
        if lo >= hi:
            raise Fail('empty window')
        # the window back to sides (nearest-first); constant elements up to
        # SMALL cells are literal
        wt = []
        for x in el[lo:hi]:
            for i in range(x[1], x[2]):
                wt.append((i, toks[i]))
        Lw, Rw = [], []
        for i, t in wt:
            if t[-1] == 'H':
                continue
            dst = Lw if i < hidx else Rw
            if t[0] == 'c':
                dst.append(('L', (t[1],)))
            else:
                e = t[2]
                if not acoefs(e) and len(t[1]) * e[0] <= SMALL:
                    dst.append(('L', C.rep(t[1], e[0])))
                else:
                    dst.append(('B', tuple(t[1]), e))
        Lw = G.fnorm(list(reversed([(x[0], tuple(reversed(x[1]))) if x[0] == 'L' else
                                    ('B', tuple(reversed(x[1])), x[2]) for x in Lw])))
        Rw = G.fnorm(Rw)
        # a constant element longer than SMALL made of literal cells: a block
        Lw = self._blockify(Lw)
        Rw = self._blockify(Rw)
        if specs['L'] is None:
            Lw = C.nstrip(Lw)
        if specs['R'] is None:
            Rw = C.nstrip(Rw)
        # the head cell: h
        exps = T.exps(Lw) + T.exps(Rw)
        for sd in ('L', 'R'):
            if specs[sd] is not None:
                exps.append(specs[sd][1])
        # neighbour relations of the window's elements (tape order)
        # (the blocks, tape order, across the head: an element the head
        # merges keeps its parts' relations), and each tail's ref against
        # the block nearest it
        wbl = [x[2] for x in reversed(Lw) if x[0] == 'B'] + [x[2] for x in Rw if x[0] == 'B']
        wrel = []
        for x, y in zip(wbl, wbl[1:]):
            wrel.append(rel_of(False, a, x, y))
        for sd, blk in (('L', wbl[:1]), ('R', wbl[-1:])):
            if specs[sd] is not None and blk:
                wrel.append(rel_of(True, 1, blk[0], specs[sd][1]))
        key = (q, h, T.shape(Lw), T.shape(Rw),
               None if specs['L'] is None else specs['L'][0],
               None if specs['R'] is None else specs['R'][0], tuple(wrel))
        if key not in self.fidx:
            if len(self.fams) >= G.MAXFAM:
                raise Fail('too many families')
            self.fidx[key] = len(self.fams)
            self.fams.append(LFam(key))
            if VERBOSE:
                print('  new family %d: %s' % (len(self.fams) - 1, fmt_key(key)),
                      file=sys.stderr)
        fid = self.fidx[key]
        F = self.fams[fid]
        ch = False
        if F.match(exps) is None:
            ch = F.join(exps)
            if F.match(exps) is None:
                raise Fail('join does not cover its target')
        return fid, exps, ch, folds

    def _blockify(self, side):
        out = []
        u = self.lang.unit
        for x in side:
            if x[0] != 'L':
                out.append(x)
                continue
            w = tuple(x[1])
            i = 0
            lit = []
            while i < len(w):
                n = 0
                while w[i + n:i + n + 1] == u:
                    n += 1
                if n > SMALL:
                    if lit:
                        out.append(('L', tuple(lit)))
                        lit = []
                    out.append(('B', u, (n, ())))
                    i += n
                else:
                    lit.extend(w[i:i + max(n, 1)])
                    i += max(n, 1)
            if lit:
                out.append(('L', tuple(lit)))
        return out


def fmt_seg(x):
    if x[0] == 'L':
        return ''.join(map(str, x[1]))
    return '%s^%s' % (''.join(map(str, x[1])), fmt_ae(x[2]))


def fmt_ae(e):
    if not e[1]:
        return str(e[0])
    return '(' + '+'.join(['%d' % e[0]] + ['%dx%d' % (a, k) for k, a in e[1]]) + ')'


def fmt_key(key):
    q, h, sL, sR, tL, tR, wrel = key
    return '%s%d L=%s R=%s tL=%s tR=%s w=%s' % (
        'ABCD'[q], h, [x[0] + (''.join(map(str, x[1]))) for x in sL],
        [x[0] + (''.join(map(str, x[1]))) for x in sR], fmt_st(tL), fmt_st(tR), wrel)


def fmt_st(s):
    if s is None:
        return '-'
    if s == 'L0':
        return 'L0'
    if s[0] == 'F':
        return 'F%s' % (s[1],)
    if s[0] == 'R':
        return 'R{%s}' % ','.join(sorted(str(x) for x in s[1]))
    return str(s)


# --------------------------------------------------------------- boot ----

def boot_of(X, tab, t0):
    r = G.run_rec(X.tabw, t0)
    if r is None:
        raise Fail('halts')
    q, L, h, R, t0 = r
    X.t0 = t0
    Ls = G.fnorm([('L', tuple(L))])
    Rs = G.fnorm([('L', tuple(R))])
    Ls = X._blockify(C.nstrip(Ls))
    Rs = X._blockify(C.nstrip(Rs))
    return q, Ls, h, Rs, {'L': None, 'R': None}, {'L': [], 'R': []}


def explore_row(spec, lang, t0, mir=False, ndata=G.NDATA):
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        raise Fail('halts')
    pins = set(k for k in tab if k not in r2[4])
    X = X3(tab, pins, lang)
    boot = boot_of(X, tab, t0)
    if ndata:
        X.data_pass(boot, ndata)
    X.explore(boot)
    return X, pins, boot


def find_dir(spec, lang, t0, mir=False, ndata=G.NDATA, plist=G.PLIST):
    X, pins, boot = explore_row(spec, lang, t0, mir, ndata)
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    cert = assemble2(X, X.t0, pins)
    cert['mir'] = mir
    tabw = X.tabw
    err = G.c_fams_ok(cert, tabw)
    if err:
        return dict(err='fams: ' + err, nfam=len(cert['fams']))
    err = G.c_boot_ok(cert, tab, tabw)
    if err:
        return dict(err=err)
    fired = [G.leaf_fired(tabw, lf) for lf in cert['leaves']]
    last = None
    for P in plist:
        lv = G.l_live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = G.c_check(cert, tab) or (None if c_maxs_ok(cert) else 'maxs')
            if err:
                return dict(err='check: ' + err)
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


# ------------------------------------------------- ListGlue2Tr: upper bounds

def c_maxget(cert, left, s):
    for l_, st, v in cert.get('maxs', []):
        if l_ == left and st == s:
            return v
    return None


def c_rubound(tr, md):
    """ListGlue2Tr.rubound"""
    a, dp, dn = tr['a'], tr['dp'], tr['dn']
    if tr['up']:
        if a == 0 or md is None:
            return None
        return (md + dn) // a
    if a == 0:
        return dp
    if md is None:
        return None
    return a * md + dp


def c_maxs_ok(cert):
    """ListGlue2Tr.maxs_ok"""
    for l_, st, v in cert.get('maxs', []):
        if G.c_accb(cert, l_, st):
            return False
        for tr in cert['trans']:
            if tr['left'] != l_ or tr['src'] != st:
                continue
            b = c_rubound(tr, c_maxget(cert, tr['left'], tr['dst']))
            if b is None or b > v:
                return False
    return True


def c_uleaves2(cert, ut, fuel, u, pL, pR, iL, iR):
    if fuel == 0 or u is None or u >= len(ut):
        return None
    nd = ut[u]
    if nd[0] == 'void':
        left = nd[1] == 'L'
        p = pL if left else pR
        if p is None:
            return None
        s, r = p
        if G.anocoef(r) and r[0] < G.c_mget(cert, left, s):
            return []
        mx = c_maxget(cert, left, s)
        if mx is not None and mx < r[0]:
            return []
        return None
    return _c_uleaves_orig(cert, ut, fuel, u, pL, pR, iL, iR)


_c_uleaves_orig = G.c_uleaves
G.c_uleaves = c_uleaves2


def assemble2(X, t0, pins):
    cert = G.assemble(X, t0, pins)
    # the state numbering of lg_batch.assemble: the transitions' states in order
    sid = {}
    for (sd, src, k, dst, rel) in X.nfa.trans:
        for st in (src, dst):
            if (sd, st) not in sid:
                sid[(sd, st)] = len(sid)
    mx = nfa_maxs(X.nfa)
    cert['maxs'] = sorted((sd == 'L', sid[(sd, st)], v) for (sd, st), v in mx.items())
    return cert


# ----------------------------------------------------------- rendering ----

def render2(c):
    """lg_batch.render for ListGlue2Tr (mkLC2, the upper bounds after the
    lower ones)"""
    s = G.r_cert(c)
    head = '(mkLC '
    assert s.startswith(head)
    lines = s.split('\n')
    # line 4 (0-based) is the mins
    mx = '[' + ';'.join('(%s,%d,%d)' % (G.r_bool(l), st, v) for l, st, v in c.get('maxs', [])) + ']'
    lines.insert(5, '      ' + mx)
    s = '(mkLC2 ' + '\n'.join(lines)[len(head):]
    lemma = 'lg2_sound_mirror' if c.get('mir') else 'lg2_sound'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, s)
