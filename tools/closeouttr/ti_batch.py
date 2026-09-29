#!/usr/bin/env python3
"""Multi-index block-family glue -> closeout batches (UNTRUSTED finder +
batch writer), for theories/Counters/TriGlueTr.v.

    python3 tools/closeouttr/ti_batch.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 120]
    python3 tools/closeouttr/ti_batch.py batch OUT.jsonl [...] --tag TI [--chunk 20]

The rows of SCOPING_INSTR.md §7.4.TI keep three or more blocks and change
lap by remainder (a block shrinks by 3 a lap, and the round's end depends
on what is left).  The certificate is TriGlueTr's [tcert]:

  * FAMILIES: symbolic tapes [q, h, L, R], each side a list of literal words
    and blocks [u^(lb + x_k)] over the family's variables;
  * a DISPATCH TREE per family, whose leaves are regions
    [x_k = M_k z_k + c_k];
  * per leaf ONE LapDecider chain from the region's instance to (the lift
    of) a family at values affine in [z];
  * a residue modulus [P], a node set closed under the steps, and per
    instruction an affine ranking that drops at every step out of a leaf
    that does not fire it into another that does not.

`find` builds all of it by symbolic execution from a boot configuration:

  1. run the wrapped machine T0 steps; the tape, with every run of at least
     two copies of 1 / 01 / 10 read as a block, is the boot family;
  2. explore every family: from its generic instance, run concretely until
     the head is about to enter a block (the start block is crossed by
     SCycR/SCycL when its traversal cycles, else peeled: its variable is
     split, small values one by one, the rest by residue); stop when the
     head is about to enter any other block.  The end configuration,
     normalized exactly as the checker does, is an instance of a (new or
     known) family, lower bounds dropping as needed;
  3. search the rankings (scipy's milp) over the reachable nodes, for
     P = 1, 2, 3, 4, 6;
  4. replay every check of [tri_check] in Python (ti_coq.py) before
     writing the certificate.

Rows whose exploration does not close (the doubling tapes and block-digit
counters grow new blocks forever) or whose instructions admit no ranking
(liveness through a remainder a mod-P node cannot see) are reported, not
written.  Everything is re-checked by the kernel ([tri_check] under
[vm_compute]); a wrong certificate fails to compile, it cannot mis-prove.
Only rows still in closeouttr_remaining.txt are written.  Compile each
batch before committing; drop a row Coq rejects with --skip SPEC.  Then
run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import collections
import json
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ti_coq as C                              # noqa: E402
from cbt import REPO, next_free, write_batch    # noqa: E402

LC = C.LC
ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']
GEN_MIN = 2
T0 = 3000
MAXFAM = 120
MAXLEAF = 600
MAXSTEPS = 4000
MAXNA = 8
QH_BOOT_CAP = 4096        # SweepGlueTr.sw_boot_cap


class Fail(Exception):
    pass


class Req(Exception):
    def __init__(self, kind, k, n):
        super().__init__(kind)
        self.kind, self.k, self.n = kind, k, n


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def mirror(tab):
    return {k: (None if v is None else (v[0], -v[1], v[2])) for k, v in tab.items()}


def run_conc(tab, n):
    """(q, L, h, R, fired) after n steps (sides nearest-first), or None"""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    fired = set()
    for _ in range(n):
        h = tape.get(pos, 0)
        tr = tab[(q, h)]
        if tr is None:
            return None
        fired.add((q, h))
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
        lo, hi = min(lo, pos), max(hi, pos)
    h = tape.get(pos, 0)
    L = tuple(tape.get(pos - 1 - j, 0) for j in range(pos - lo))
    R = tuple(tape.get(pos + 1 + j, 0) for j in range(hi - pos))
    return q, L, h, R, fired


# ------------------------------------------------------------ families ----

def _prim_units(maxlen):
    out = []
    for n in range(1, maxlen + 1):
        for x in range(2 ** n):
            u = tuple((x >> (n - 1 - i)) & 1 for i in range(n))
            if C.primroot(u)[1] == 1 and any(u):
                out.append(u)
    return out


GEN_UNITS = _prim_units(4)


def generalize(side):
    """literal runs of >= GEN_MIN copies of a unit become constant blocks
    (the unit covering the most cells wins, the shorter one on a tie)"""
    out = []
    for s in side:
        if s[0] != 'L':
            out.append(s)
            continue
        w = tuple(s[1])
        i = 0
        lit = []
        while i < len(w):
            best = None
            for u in GEN_UNITS:
                k = len(u)
                n = 0
                while w[i + k * n:i + k * (n + 1)] == u:
                    n += 1
                if n >= GEN_MIN and (best is None or k * n > len(best[0]) * best[1]):
                    best = (u, n)
            if best:
                if lit:
                    out.append(('L', tuple(lit)))
                    lit = []
                out.append(('B', best[0], (best[1], ())))
                i += len(best[0]) * best[1]
            else:
                lit.append(w[i])
                i += 1
        if lit:
            out.append(('L', tuple(lit)))
    return out


def shape(side):
    return tuple(('L', tuple(s[1])) if s[0] == 'L' else ('B', tuple(s[1])) for s in side)


def exps(side):
    return [s[2] for s in side if s[0] == 'B']


class Fam:
    def __init__(self, key, lb):
        self.key = key
        self.q, self.h, self.sL, self.sR = key
        self.lb = list(lb)
        self.n = len(lb)

    def pattern(self):
        k = 0
        out = []
        for sh in (self.sL, self.sR):
            side = []
            for s in sh:
                if s[0] == 'L':
                    side.append(s)
                else:
                    side.append(('B', s[1], (self.lb[k], ((k, 1),))))
                    k += 1
            out.append(side)
        return out


# ---------------------------------------------------------------- leaf ----

def cprefix(segs, i):
    pre = ()
    while i < len(segs):
        s = segs[i]
        if s[0] == 'L':
            pre += tuple(s[1])
        elif not s[2][1]:
            pre += C.rep(s[1], s[2][0])
        else:
            break
        i += 1
    return pre, i


def cyc_R(tab, q, h, u, nmax=400):
    cfg = (q, (), h, tuple(u))
    for n in range(1, nmax + 1):
        try:
            cfg = LC.wstep(tab, True, True, cfg)
        except LC.Halt:
            return None
        if cfg is None:
            return None
        q2, l2, h2, r2 = cfg
        if not r2 and q2 == q and h2 == h:
            return n
    return None


def cyc_L(tab, q, h, u, rpre, nmax=400):
    for m in range(len(rpre) + 1):
        rw = tuple(rpre[:m])
        cfg = (q, tuple(u), h, rw)
        for n in range(1, nmax + 1):
            try:
                cfg = LC.wstep(tab, True, True, cfg)
            except LC.Halt:
                break
            if cfg is None:
                break
            q2, l2, h2, r2 = cfg
            if not l2 and q2 == q and h2 == h and r2[:len(rw)] == rw:
                return n, m
    return None


def merge_chain(ch):
    out = []
    for st in ch:
        if out and st[0] in ('SWin', 'SWinL', 'SWinR') and out[-1][0] == st[0]:
            out[-1] = (st[0], out[-1][1] + st[1])
        else:
            out.append(st)
    return out


def leaf_run(tabw, fam, R, na, p):
    pat = fam.pattern()
    sub = C.rsub(R)
    Lz = [C.seg_subst(sub, x) for x in pat[0]]
    Rz = [C.seg_subst(sub, x) for x in pat[1]]
    q, h = fam.q, fam.h
    tr = tabw.get((q, h))
    if tr is None:
        raise Fail('pinned at a family start')
    D = 'R' if tr[1] > 0 else 'L'
    Dz, Oz = (Rz, Lz) if D == 'R' else (Lz, Rz)
    dpre, i = cprefix(Dz, 0)
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
        post, i2 = cprefix(Dz, i + 1)
        dss = (C.rep(u, na), C.rep(u, p), a // p, b, C.rep(u, r) + post)
        nD = i2
        idx = (k, D, u)
    else:
        dss = (dpre, (), 0, 0, ())
        nD = i
    opre, nO = cprefix(Oz, 0)
    oss = (opre, (), 0, 0, ())
    if D == 'R':
        c0 = (q, oss, h, dss)
        nL, nR = nO, nD
    else:
        c0 = (q, dss, h, oss)
        nL, nR = nD, nO
    el, er = nL >= len(Lz), nR >= len(Rz)
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

    while True:
        if nsteps > MAXSTEPS:
            raise Fail('leaf too long')
        q1, L1, h1, R1 = c
        tr = tabw.get((q1, h1))
        if tr is None:
            raise Fail('pinned inside a leaf')
        # the start block adjacent and not crossed yet: try to cross it now
        if idx is not None and not crossed:
            bs = R1 if idx[1] == 'R' else L1
            if not bs[0] and bs[1]:
                if idx[1] == 'R':
                    n = cyc_R(tabw, q1, h1, bs[1])
                    if n is not None:
                        emit(('SCycR', n))
                        crossed = True
                        nsteps += 1
                        continue
                else:
                    r = cyc_L(tabw, q1, h1, bs[1], R1[0])
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
                        ok = (cyc_R(tabw, q1, h1, U2) is not None) if d > 0 \
                            else cyc_L(tabw, q1, h1, U2, R1[0]) is not None
                        if ok:
                            raise Req('pow', idx[0], p2)
                if nsteps > 0:
                    break               # back at the start block after an excursion: cut
                if na >= MAXNA:
                    raise Fail('no cycle through the start block')
                raise Req('na', idx[0], na + 1)
            break                       # the crossed block, behind: cut
        X = (Rz[nR:] if d > 0 else Lz[nL:])
        if X:
            break                       # an opaque block: cut
        emit(('SWinR', 1) if d > 0 else ('SWinL', 1))
        nsteps += 1
    if nsteps == 0:
        raise Fail('empty leaf')
    chain = merge_chain(chain)
    # the step count ca * z_j + cb must be positive for every z
    r = LC.srun(tabw, el, er, chain, c0)
    if r is None:
        raise Fail('chain does not replay')
    c1, ca, cb = r
    if cb == 0:
        if idx is None:
            raise Fail('zero-step leaf')
        raise Req('ge', idx[0], 1 + (0 if dss[3] or dss[0] else 0))
    endL = C.ss_segs(c1[1], j) + Lz[nL:]
    endR = C.ss_segs(c1[3], j) + Rz[nR:]
    return dict(c0=c0, el=el, er=er, chain=chain, j=j, nL=nL, nR=nR, c1=c1,
                q1=c1[0], h1=c1[2], endL=endL, endR=endR, Lz=Lz, Rz=Rz)


# ------------------------------------------------------------- explore ----

class Explorer:
    def __init__(self, tab, pins):
        self.tab = tab
        self.tabw = {k: (None if k in pins else v) for k, v in tab.items()}
        self.fams = []
        self.fidx = {}
        self.trees = {}         # fid -> nodes
        self.fleaves = {}       # fid -> [leaf dicts]

    def fam_of(self, q, h, L, R):
        """(fid, exps, lowered?) for a normalized configuration"""
        L = generalize(L)
        R = generalize(R)
        key = (q, h, shape(L), shape(R))
        ex = exps(L) + exps(R)
        if key not in self.fidx:
            if len(self.fams) >= MAXFAM:
                raise Fail('too many families')
            self.fidx[key] = len(self.fams)
            self.fams.append(Fam(key, [e[0] for e in ex]))
            return self.fidx[key], ex, True
        fid = self.fidx[key]
        F = self.fams[fid]
        low = False
        for i, e in enumerate(ex):
            if e[0] < F.lb[i]:
                F.lb[i] = e[0]
                low = True
        return fid, ex, low

    def explore(self, boot):
        q, L, h, R = boot
        f0, ex0, _ = self.fam_of(q, h, L, R)
        self.boot = (f0, [e[0] for e in ex0])
        todo = [f0]
        while todo:
            fid = todo.pop(0)
            if fid in todo:
                continue
            self.explore_fam(fid, todo)

    def explore_fam(self, fid, todo):
        F = self.fams[fid]
        lb0 = list(F.lb)
        nodes = []
        leaves = []

        def build(R, na, p):
            if len(leaves) > MAXLEAF:
                raise Fail('too many leaves')
            while True:
                try:
                    lf = leaf_run(self.tabw, F, R, na, p)
                    break
                except Req as rq:
                    k = rq.k
                    M, c = R[k]
                    if rq.kind == 'na':
                        na = rq.n
                        continue
                    me = len(nodes)
                    nodes.append(None)
                    if rq.kind == 'ge':
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
                    else:
                        pp = rq.n
                        kids = []
                        for s in range(pp):
                            R2 = list(R)
                            R2[k] = (M * pp, c + M * s)
                            kids.append(build(R2, na, pp))
                        nodes[me] = ('split', k, 0, pp, kids)
                    return me
            me = len(nodes)
            nodes.append(('leaf', len(leaves)))
            Ln = C.nstrip(C.norm(lf['endL']))
            Rn = C.nstrip(C.norm(lf['endR']))
            g, ex, low = self.fam_of(lf['q1'], lf['h1'], Ln, Rn)
            lf.update(reg=list(R), g=g, ex=ex)
            leaves.append(lf)
            if low or g not in self.fleaves:
                if g not in todo:
                    todo.append(g)
            return me

        build([(1, 0)] * F.n, 0, 1)
        if F.lb != lb0:
            todo.append(fid)
            return
        self.trees[fid] = nodes
        self.fleaves[fid] = leaves


# ---------------------------------------------------------------- cert ----

def assemble(X, t0, mir, pins):
    """the certificate (P, S, ranks still missing), leaves numbered globally"""
    fids = sorted(X.fleaves)
    gl = {}
    leaves = []
    fams = []
    for f in range(len(X.fams)):
        if f not in X.fleaves:
            raise Fail('unexplored family %d' % f)
    for f in range(len(X.fams)):
        F = X.fams[f]
        base = len(leaves)
        for i, lf in enumerate(X.fleaves[f]):
            G = X.fams[lf['g']]
            tgt = [C.aaddc(e, -l) for e, l in zip(lf['ex'], G.lb)]
            if any(e[0] < 0 for e in tgt):
                raise Fail('target below a lower bound')
            leaves.append(dict(f=f, reg=lf['reg'], g=lf['g'], tgt=tgt, c0=lf['c0'], j=lf['j'],
                               el=lf['el'], er=lf['er'], nL=lf['nL'], nR=lf['nR'],
                               chain=lf['chain']))
        nodes = [(('leaf', base + nd[1]) if nd[0] == 'leaf' else nd) for nd in X.trees[f]]
        pat = F.pattern()
        fams.append(dict(q=F.q, h=F.h, L=pat[0], R=pat[1], n=F.n, tree=nodes))
    f0, v0 = X.boot
    v0 = [v - l for v, l in zip(v0, X.fams[f0].lb)]
    return dict(pins=sorted(pins), fams=fams, leaves=leaves, t0=t0, f0=f0, v0=v0, mir=mir)


def leaf_ok(tabw, fams, F, lf):
    """TriGlueTr.leaf_ok"""
    if lf['g'] >= len(fams):
        return False
    G = fams[lf['g']]
    sub = C.rsub(lf['reg'])
    Lz = [C.seg_subst(sub, x) for x in F['L']]
    Rz = [C.seg_subst(sub, x) for x in F['R']]
    c0 = lf['c0']
    try:
        r = LC.srun(tabw, lf['el'], lf['er'], lf['chain'], c0)
    except LC.Halt:
        r = None
    if r is None:
        return False
    c1, ca, cb = r
    j = lf['j']
    tsub = lf['tgt']
    return (c0[0] == F['q'] and c0[2] == F['h']
            and C.same_segs(C.ss_segs(c0[1], j) + Lz[lf['nL']:], Lz)
            and C.same_segs(C.ss_segs(c0[3], j) + Rz[lf['nR']:], Rz)
            and (not lf['el'] or len(Lz) <= lf['nL'])
            and (not lf['er'] or len(Rz) <= lf['nR'])
            and c1[0] == G['q'] and c1[2] == G['h']
            and C.lsame_segs(C.ss_segs(c1[1], j) + Lz[lf['nL']:],
                             [C.seg_subst(tsub, x) for x in G['L']])
            and C.lsame_segs(C.ss_segs(c1[3], j) + Rz[lf['nR']:],
                             [C.seg_subst(tsub, x) for x in G['R']])
            and cb > 0 and len(tsub) == G['n'] and len(lf['reg']) == F['n'])


def fams_ok(tabw, cert):
    fams, lvs = cert['fams'], cert['leaves']
    for fi, F in enumerate(fams):
        L = C.tleaves(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'])
        if L is None:
            return 'bad tree %d' % fi
        for l, R in L:
            if l >= len(lvs):
                return 'bad leaf index'
            lf = lvs[l]
            if lf['f'] != fi or [tuple(x) for x in lf['reg']] != [tuple(x) for x in R]:
                return 'leaf %d misfiled' % l
            if not leaf_ok(tabw, fams, F, lf):
                return 'leaf %d fails' % l
    return None


def tinst(F, vals):
    return (F['q'], C.sided(vals, F['L']), F['h'], C.sided(vals, F['R']))


def nodeidx(cert, S, P, fi, vals):
    F = cert['fams'][fi]
    r = C.twalk(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'], vals)
    if r is None:
        return None
    rho = [v % P for v in vals]
    try:
        return S.index((r[0], tuple(rho)))
    except ValueError:
        return None


def edges(cert, P, tabw, node):
    """[(s, src, tgt, rho', [candidate leaves])] of one node"""
    l, rho = node
    lvs = cert['leaves']
    lf = lvs[l]
    out = []
    for s in C.sassign(P, lf['reg'], list(rho)):
        sub = C.zsub(P, s)
        src = [C.asubst(sub, e) for e in C.rsub(lf['reg'])]
        tgt = [C.asubst(sub, e) for e in lf['tgt']]
        if not all(C.pdiv(P, e) for e in tgt):
            return None
        rho2 = tuple(e[0] % P for e in tgt)
        cands = [l2 for l2, lf2 in enumerate(lvs)
                 if lf2['f'] == lf['g'] and C.compat(P, lf2['reg'], tgt)]
        out.append((s, src, tgt, rho2, cands))
    return out


def live_search(cert, tabw, fired, P):
    """closed node set from the boot, then a ranking per instruction"""
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    F0 = cert['fams'][cert['f0']]
    r = C.twalk(F0['tree'], len(F0['tree']), 0, [(1, 0)] * F0['n'], cert['v0'])
    if r is None:
        return None
    b = (r[0], tuple(v % P for v in cert['v0']))
    S = [b]
    seen = {b}
    E = {}
    k = 0
    while k < len(S):
        nd = S[k]
        k += 1
        es = edges(cert, P, tabw, nd)
        if es is None:
            return None
        E[nd] = es
        for s, src, tgt, rho2, cands in es:
            for l2 in cands:
                n2 = (l2, rho2)
                if n2 not in seen:
                    seen.add(n2)
                    S.append(n2)
        if len(S) > 3000:
            return None
    pos = {nd: i for i, nd in enumerate(S)}
    nv = {nd: cert['fams'][cert['leaves'][nd[0]]['f']]['n'] for nd in S}
    off = {}
    n = 0
    for nd in S:
        off[nd] = n
        n += 1 + nv[nd]
    ranks = []
    for q in range(4):
        for h in range(2):
            t = (q, h)
            if t in cert['pins']:
                continue
            A, lo = [], []
            for nd in S:
                if t in fired[nd[0]]:
                    continue
                for s, src, tgt, rho2, cands in E[nd]:
                    for l2 in cands:
                        if t in fired[l2]:
                            continue
                        n2 = (l2, rho2)
                        o, o2 = off[nd], off[n2]
                        # V(src) >= V'(tgt) + 1, coefficient-wise over z'
                        params = sorted(set(p for e in src + tgt for p, _ in e[1]))
                        row = np.zeros(n)
                        row[o] += 1
                        row[o2] -= 1
                        for kk, e in enumerate(src[:nv[nd]]):
                            row[o + 1 + kk] += e[0]
                        for kk, e in enumerate(tgt[:nv[n2]]):
                            row[o2 + 1 + kk] -= e[0]
                        A.append(row)
                        lo.append(1)
                        for p in params:
                            row = np.zeros(n)
                            for kk, e in enumerate(src[:nv[nd]]):
                                row[o + 1 + kk] += C.tcoef(p, e[1])
                            for kk, e in enumerate(tgt[:nv[n2]]):
                                row[o2 + 1 + kk] -= C.tcoef(p, e[1])
                            A.append(row)
                            lo.append(0)
            if not A:
                continue
            A = np.array(A)
            res = milp(c=np.ones(n), constraints=LinearConstraint(A, np.array(lo), np.inf),
                       integrality=np.ones(n), bounds=Bounds(0, 10 ** 6))
            if not res.success:
                return ('norank', t)
            x = np.round(res.x).astype(int)
            if (A @ x < np.array(lo)).any():
                return ('norank', t)
            V = [(int(x[off[nd]]), [int(y) for y in x[off[nd] + 1:off[nd] + 1 + nv[nd]]])
                 for nd in S]
            ranks.append((t, V))
    return dict(P=P, S=[(l, list(rho)) for l, rho in S], ranks=ranks)


def live_ok(cert, tabw, fired):
    """TriGlueTr.live_ok"""
    P = cert['P']
    if P <= 0:
        return 'P'
    S = [(l, tuple(r)) for l, r in cert['S']]
    rk = dict((tuple(t), V) for t, V in cert['ranks'])
    lvs = cert['leaves']
    for i, nd in enumerate(S):
        if nd[0] >= len(lvs):
            return 'node leaf'
        es = edges(cert, P, tabw, nd)
        if es is None:
            return 'pdiv'
        for s, src, tgt, rho2, cands in es:
            for l2 in cands:
                try:
                    i2 = S.index((l2, rho2))
                except ValueError:
                    return 'not closed'
                for q in range(4):
                    for h in range(2):
                        t = (q, h)
                        if t in cert['pins'] or t in fired[nd[0]] or t in fired[l2]:
                            continue
                        Vs = rk.get(t, [])
                        V = Vs[i] if i < len(Vs) else (0, [])
                        V2 = Vs[i2] if i2 < len(Vs) else (0, [])
                        if not C.ale(C.aaddc(C.veval(V2, tgt), 1), C.veval(V, src)):
                            return 'rank %s at node %d' % (t, i)
    return None


def boot_ok(cert, tab):
    """boot_ok (DN: on the wrapped machine) / boot_qh_ok (QH: on the machine,
    a pinned instruction fired before t0, t0 <= 4096)"""
    F = cert['fams'][cert['f0']]
    if cert.get('qh'):
        tabb = tab
        if cert['t0'] > QH_BOOT_CAP:
            return False
        tape, pos, q, hit = {}, 0, 0, False
        for _ in range(cert['t0']):
            h = tape.get(pos, 0)
            if (q, h) in cert['pins']:
                hit = True
            w, d, nq = tab[(q, h)]
            tape[pos] = w
            pos += d
            q = nq
        if not hit:
            return False
    else:
        tabb = {k: (None if k in cert['pins'] else v) for k, v in tab.items()}
    r = run_conc(tabb, cert['t0'])
    if r is None:
        return False
    q, L, h, R, _ = r
    q2, L2, h2, R2 = tinst(F, cert['v0'])
    strip = C.rstrip0
    return (q, h) == (q2, h2) and strip(L) == strip(L2) and strip(R) == strip(R2) \
        and len(cert['v0']) == F['n']


def quiet_pins(tab, lastq):
    """the instructions silent after the quiet point (and the undefined ones)"""
    n = int(1.5 * lastq) + 60000
    tape, pos, q, last = {}, 0, 0, {}
    for t in range(n):
        h = tape.get(pos, 0)
        tr = tab[(q, h)]
        if tr is None:
            return None
        last[(q, h)] = t
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
    return set(k for k in tab if k not in last or last[k] <= lastq)


def find_dir(tab, mir, qh=False, lastq=0, t0=T0):
    if qh:
        pins = quiet_pins(tab, lastq)
        if pins is None:
            return dict(err='halts')
        t0 = max(lastq + 64, min(t0, QH_BOOT_CAP))
        if t0 > QH_BOOT_CAP:
            return dict(err='quiet point past the boot cap')
        r = run_conc(tab, t0)
    else:
        r2 = run_conc(tab, 60000)
        if r2 is None:
            return dict(err='halts')
        # pins: the instructions that never fire (the undefined ones, in practice)
        pins = set(k for k in tab if k not in r2[4])
        r = run_conc(tab, t0)
    if r is None:
        return dict(err='halts')
    q, L, h, R, fired = r
    X = Explorer(tab, pins)
    boot = (q, C.nstrip(C.norm([('L', L)])), h, C.nstrip(C.norm([('L', R)])))
    X.explore(boot)
    cert = assemble(X, t0, mir, pins)
    cert['qh'] = qh
    tabw = X.tabw
    err = fams_ok(tabw, cert)
    if err:
        return dict(err='fams: ' + err)
    if not boot_ok(cert, tab):
        return dict(err='boot')
    fired = [set(C.leaf_fired(tabw, dict(chain=lf['chain'], el=lf['el'], er=lf['er'],
                                         c0=lf['c0']))) for lf in cert['leaves']]
    last = None
    for P in (1, 2, 3, 4, 6):
        lv = live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = live_ok(cert, tabw, fired)
            if err:
                return dict(err='live: ' + err)
            if nodeidx(cert, [(l, tuple(r)) for l, r in cert['S']], cert['P'], cert['f0'],
                       cert['v0']) is None:
                return dict(err='boot node')
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0, cls='DN', lastq=0):
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    errs = []
    try:
        for mir in (False, True):
            tab = parse(spec)
            if mir:
                tab = mirror(tab)
            try:
                r = find_dir(tab, mir, cls == 'QH', lastq)
            except Fail as e:
                r = dict(err=str(e))
            except RecursionError:
                r = dict(err='recursion')
            if 'err' not in r:
                r['spec'] = spec
                return r
            errs.append(r['err'])
    except Timeout:
        errs.append('timeout')
    finally:
        if timeout:
            signal.alarm(0)
    return dict(spec=spec, err=' / '.join(errs))


# -------------------------------------------------------------- render ----

def clist(xs):
    return '[' + ';'.join(SYM[x] for x in xs) + ']'


def cstep(st):
    return '(%s)' % ' '.join([st[0]] + [str(x) for x in st[1:]])


def cchain(ch):
    return '[' + '; '.join(cstep(tuple(s)) for s in ch) + ']'


def caexp(e):
    return '(mkA %d [%s])' % (e[0], ';'.join('(%d,%d)' % (k, a) for k, a in e[1]))


def cseg(s):
    if s[0] == 'L':
        return '(SL %s)' % clist(s[1])
    return '(SB %s %s)' % (clist(s[1]), caexp(s[2]))


def csegs(l):
    return '[' + ';'.join(cseg(s) for s in l) + ']'


def cside(s):
    pre, u, a, b, post = s
    return '(mkS %s %s %d %d %s)' % (clist(pre), clist(u), a, b, clist(post))


def cnode(nd):
    if nd[0] == 'leaf':
        return '(TLeaf %d)' % nd[1]
    _, k, n, p, kids = nd
    return '(TSplit %d %d %d [%s])' % (k, n, p, ';'.join(str(x) for x in kids))


def render(c):
    B = lambda x: 'true' if x else 'false'
    pins = '[' + ';'.join('(%s,%s)' % (ST[q], SYM[s]) for q, s in c['pins']) + ']'
    fams = '[' + ';\n      '.join(
        '(mkTF %s %s %s %s %d [%s])' % (ST[F['q']], SYM[F['h']], csegs(F['L']), csegs(F['R']),
                                        F['n'], ';'.join(cnode(nd) for nd in F['tree']))
        for F in c['fams']) + ']'
    leaves = '[' + ';\n      '.join(
        '(mkTL %d [%s] %d [%s] (mkC %s %s %s %s) %d %s %s %d %d %s)' % (
            lf['f'], ';'.join('(%d,%d)' % tuple(x) for x in lf['reg']), lf['g'],
            ';'.join(caexp(e) for e in lf['tgt']),
            ST[lf['c0'][0]], cside(lf['c0'][1]), SYM[lf['c0'][2]], cside(lf['c0'][3]),
            lf['j'], B(lf['el']), B(lf['er']), lf['nL'], lf['nR'], cchain(lf['chain']))
        for lf in c['leaves']) + ']'
    S = '[' + ';'.join('(%d,[%s])' % (l, ';'.join(str(x) for x in r)) for l, r in c['S']) + ']'
    ranks = '[' + ';\n      '.join(
        '((%s,%s), [%s])' % (ST[t[0]], SYM[t[1]],
                             ';'.join('(%d,[%s])' % (v[0], ';'.join(str(x) for x in v[1]))
                                      for v in V))
        for t, V in c['ranks']) + ']'
    cert = '(mkTC %s\n      %s\n      %s\n      %d %s\n      %s\n      %d %d [%s])' % (
        pins, fams, leaves, c['P'], S, ranks, c['t0'], c['f0'],
        ';'.join(str(x) for x in c['v0']))
    if c.get('qh'):
        lemma = 'tri_sound_qh_mirror' if c['mir'] else 'tri_sound_qh'
        return 'apply coversTr_qh3, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (
            lemma, cert)
    lemma = 'tri_sound_mirror' if c['mir'] else 'tri_sound'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)


def jsonable(c):
    def conv(x):
        if isinstance(x, (list, tuple)):
            return [conv(y) for y in x]
        if isinstance(x, dict):
            return {k: conv(v) for k, v in x.items()}
        if isinstance(x, set):
            return sorted(conv(y) for y in x)
        return x
    return conv(c)


def detuple(c):
    """json lists back to the tuples render/replay expect"""
    def T(x):
        return tuple(T(y) for y in x) if isinstance(x, list) else x

    def seg(s):
        return ('L', tuple(s[1])) if s[0] == 'L' else ('B', tuple(s[1]), T(s[2]))
    for F in c['fams']:
        F['L'] = [seg(s) for s in F['L']]
        F['R'] = [seg(s) for s in F['R']]
        F['tree'] = [tuple(T(x) if i < 4 else list(x) for i, x in enumerate(nd))
                     if nd[0] == 'split' else tuple(nd) for nd in F['tree']]
    for lf in c['leaves']:
        lf['c0'] = T(lf['c0'])
        lf['tgt'] = [T(e) for e in lf['tgt']]
        lf['chain'] = [tuple(s) for s in lf['chain']]
        lf['reg'] = [tuple(x) for x in lf['reg']]
    c['pins'] = [tuple(p) for p in c['pins']]
    c['ranks'] = [(tuple(t), [(v[0], list(v[1])) for v in V]) for t, V in c['ranks']]
    return c


def remaining():
    return set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))


def classes():
    out = {}
    for l in open(os.path.join(REPO, 'closeouttr_classes.tsv')):
        if l.startswith('#'):
            continue
        f = l.rstrip('\n').split('\t')
        out[f[0]] = (f[1], max(0, int(f[2])))
    return out


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    cls = classes()
    todo = [(s, a.timeout) + cls.get(s, ('DN', 0)) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(jsonable(r)) + '\n')
            f.flush()
            stats[r.get('err', 'ok').split(':')[0].split(' ')[0]] += 1
    print(dict(stats))


def cmd_batch(a):
    rem = remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(detuple(c))
    if a.limit:
        certs = certs[:a.limit]
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], render(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr.'],
                                entries, 'multi-block sweeps by the block-family glue '
                                         '(TriGlueTr, tri_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=120)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='TI')
    p.add_argument('--chunk', type=int, default=20)
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
