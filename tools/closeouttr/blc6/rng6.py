"""BLC6: BLC4's exploration with RANGE voids (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC6).

blc4/lg4.X4 splits a variable in the family's TriGlue dispatch tree when an
unfold path reaches a tail state whose certified lower bound (lc_mins) is
above the path's ref for the small values of one region parameter: one
singleton kid per small value, and every OTHER unfold path of the family is
then re-explored at those constants.  Here the void is a node of the unfold
tree itself (ListGlueRngTr's URng): z_k < n is void on this path, and the
path continues with z_k := n + z_k.  Nothing else changes.

The explore_fam below is lg4.X4.explore_fam with that one branch replaced
(marked BLC6).
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc4'))
import lg3                                        # noqa: E402
import lg4                                        # noqa: E402
import lg_batch as G                              # noqa: E402
import ti_batch as T                              # noqa: E402
import ti_coq as C                                # noqa: E402
from lg4 import NeedMod, NonCanon, Req, acoefs, Fail, nfa_maxs  # noqa: E402,F401

RNG = os.environ.get('BLC6_RNG', '1') == '1'
LOCAL = os.environ.get('BLC6_LOCAL', '1') == '1'
STATS = collections.Counter()


def shs(k, n, ln):
    """ListGlueRngTr.shs: the substitution z_k := n + z_k"""
    return [(n if i == k else 0, ((i, 1),)) for i in range(ln)]


def shift(R, paths, k, n):
    """ListGlueRngTr.shR on the region, shs (C.asubst, Coq's normal form)
    on the unfolded items"""
    M, c = R[k]
    R2 = list(R)
    R2[k] = (M, c + M * n)
    sg = shs(k, n, len(R))
    p2 = {}
    for sd, pt in paths.items():
        p2[sd] = [ent if ent == 'end' else (ent[0], C.asubst(sg, ent[1])) for ent in pt]
    return R2, p2


def sps(k, e, ln):
    """ListGlueRngTr.sps: z_k := e"""
    return [e if i == k else (0, ((i, 1),)) for i in range(ln)]


def split_kid(R, paths, k, n, pp, j):
    """ListGlueRngTr's USpl kid j: the region (sreg) and the unfolded items
    substituted by sps k (skid k n pp j)"""
    M, c = R[k]
    R2 = list(R)
    if j < n:
        R2[k] = (0, c + M * j)
        e = (j, ())
    else:
        R2[k] = (M * pp, c + M * j)
        e = (j, ((k, pp),))
    sg = sps(k, e, len(R))
    p2 = {}
    for sd, pt in paths.items():
        p2[sd] = [ent if ent == 'end' else (ent[0], C.asubst(sg, ent[1])) for ent in pt]
    return R2, p2


class X6(lg4.X4):
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
            """run_unf0, with every request this path raises answered by a
            split LOCAL to the path (ListGlueRngTr's USpl) instead of one in
            the family's TriGlue tree"""
            if not LOCAL:
                return run_unf0(R, paths, na, p)
            while True:
                u0, l0 = len(unodes), len(leaves)
                try:
                    return run_unf0(R, paths, na, p)
                except Up as up:
                    rq = up.rq
                    del unodes[u0:]
                    del leaves[l0:]
                if rq.kind not in ('ge', 'uge', 'mod', 'pow', 'umod'):
                    raise Up(rq)
                k = rq.k
                M, c = R[k]
                STATS['l_' + rq.kind] += 1
                me = len(unodes)
                unodes.append(None)
                kids = []
                if rq.kind in ('ge', 'uge'):
                    n, pp = rq.n, 1
                    for v in range(n):
                        R2, p2 = split_kid(R, paths, k, n, pp, v)
                        kids.append(run_unf(R2, p2, 0, 1))
                    R2, p2 = split_kid(R, paths, k, n, pp, n)
                    kids.append(run_unf(R2, p2, na, p))
                else:
                    n, pp = 0, rq.n
                    for s_ in range(pp):
                        R2, p2 = split_kid(R, paths, k, n, pp, s_)
                        kids.append(run_unf(R2, p2, na, p if rq.kind == 'umod' else pp))
                unodes[me] = ('spl', k, n, pp, kids)
                return me

        def run_unf0(R, paths, na, p):
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
                        n = -(-(mm - r_[0]) // m_)
                        if RNG:
                            # BLC6: void z_k < n on THIS path only (URng),
                            # the rest reparametrised z_k := n + z_k
                            STATS['rng'] += 1
                            R2, paths2 = shift(R, paths, k, n)
                            me = len(unodes)
                            unodes.append(None)
                            unodes[me] = ('rng', sd, k, n, run_unf(R2, paths2, na, p))
                            return me
                        STATS['uge'] += 1
                        raise Up(Req('uge', k, n))
                mx = self.maxs.get((sd, s_))
                if mx is not None:
                    if r_[0] > mx:
                        me = len(unodes)
                        unodes.append(('void', sd))
                        return me
                    cs = acoefs(r_)
                    if len(cs) == 1:
                        k, m_ = cs[0]
                        STATS['ugemax'] += 1
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
            except NeedMod as nm:
                raise Up(Req('umod', nm.k, nm.m))
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
                    STATS['g_' + rq.kind] += 1
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




def explore_row(spec, lang, t0, mir=False):
    """lg4.explore_row with X6"""
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        raise Fail('halts')
    pins = set(k for k in tab if k not in r2[4])
    lg4.CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
    X = X6(tab, pins, lang)
    boot = lg3.boot_of(X, tab, t0)
    X.explore(boot)
    return X, pins, boot
