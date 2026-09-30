#!/usr/bin/env python3
"""Lexicographic l-adic liveness for TriGlue family graphs (UNTRUSTED finder),
for theories/Counters/TriNuTr.v.

    python3 tools/closeouttr/ta/nu_find.py DUMP.jsonl OUT.jsonl [--plist 1,2,3,4,6] [--ells 2,3]

DUMP.jsonl is the output of ta/dump.py: TriGlue certificates whose family
set closes but whose per-instruction affine rankings do not exist.  For
each such row and each instruction t, this searches, on TriGlue's closed
node set S (nodes = (leaf, values mod P)), for

  * a LEVEL per node that never goes up along an edge between two nodes
    whose leaves do not fire t (the SCCs of that graph, topologically);
  * inside a level, an affine form E_i >= 1 per node and a prime l with,
    on every such edge i -> i' (both sides affine in the leaf parameters z),

        B * E_i(src(z)) = A * E_i'(tgt(z))   coefficient-wise,
        gcd(B, l) = 1,  A = b * l^j,  gcd(b, l) = 1,

    so nu_l(E_i') = nu_l(E_i) - j: the l-adic valuation never rises;
  * an affine ranking V_i that drops by one on every edge with j = 0.

(level, nu_l(E), V) then decreases lexicographically at every step between
non-firing nodes, so t fires from every anchor.  E is found as a common
"eigen-form" of the SCC: ratio 1 on a spanning tree (every E can be
rescaled so), each other edge's ratio r from a small candidate set by
exact rank tests, the l-power split into node potentials, then V and the
potentials by one MILP.  Everything is replayed exactly (nu_check) before a
certificate is written; the kernel re-checks it all.
"""
import argparse
import itertools
import json
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ti_batch as T                            # noqa: E402
import ti_coq as C                              # noqa: E402

RCANDS = sorted(set(Fr(p, q) for p in range(1, 28) for q in range(1, 28)))


class Fail(Exception):
    pass


# ------------------------------------------------------------ rationals ----

def rank_null(M, ncols):
    """exact nullspace basis (list of column vectors) of the rows M"""
    A = [list(map(Fr, r)) for r in M]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fr(0)] * ncols
        v[fc] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis


def matmul(A, B):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def nu(l, x):
    x = Fr(x)
    if x == 0:
        return 10 ** 9
    n, d, k = x.numerator, x.denominator, 0
    while n % l == 0:
        n //= l
        k += 1
    while d % l == 0:
        d //= l
        k -= 1
    return k


# -------------------------------------------------------------- graph ----

def closed_nodes(cert, P, tabw):
    F0 = cert['fams'][cert['f0']]
    r = C.twalk(F0['tree'], len(F0['tree']), 0, [(1, 0)] * F0['n'], cert['v0'])
    if r is None:
        raise Fail('boot walk')
    b = (r[0], tuple(v % P for v in cert['v0']))
    S, seen, E, k = [b], {b}, {}, 0
    while k < len(S):
        nd = S[k]
        k += 1
        es = T.edges(cert, P, tabw, nd)
        if es is None:
            raise Fail('pdiv')
        E[nd] = es
        for s, src, tgt, rho2, cands in es:
            for l2 in cands:
                n2 = (l2, rho2)
                if n2 not in seen:
                    seen.add(n2)
                    S.append(n2)
        if len(S) > 3000:
            raise Fail('too many nodes')
    return S, E


def sccs(nodes, succ):
    idx, low, on, st, out, cnt = {}, {}, set(), [], [], [0]
    for v0 in nodes:
        if v0 in idx:
            continue
        work = [(v0, iter(succ[v0]))]
        idx[v0] = low[v0] = cnt[0]
        cnt[0] += 1
        st.append(v0)
        on.add(v0)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is not None:
                if w not in idx:
                    idx[w] = low[w] = cnt[0]
                    cnt[0] += 1
                    st.append(w)
                    on.add(w)
                    work.append((w, iter(succ[w])))
                elif w in on:
                    low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == idx[v]:
                    comp = []
                    while True:
                        w = st.pop()
                        on.discard(w)
                        comp.append(w)
                        if w == v:
                            break
                    out.append(comp)
    return out


# ------------------------------------------------------ eigen-forms ----

def lin(exprs, n, m):
    """the (m+1) x (n+1) matrix of e -> E(exprs) over z: row 0 constant,
    row 1+p the coefficient of z_p; column 0 E's constant, 1+k its x_k"""
    M = [[Fr(0)] * (n + 1) for _ in range(m + 1)]
    M[0][0] = Fr(1)
    for k in range(n):
        e = exprs[k]
        M[0][k + 1] = Fr(e[0])
        for p, a in e[1]:
            M[p + 1][k + 1] += a
    return M


def find_E(comp, cedges, nv):
    """per node an E (list of Fractions: const, coefs) with every edge
    proportional; None if none"""
    off, n = {}, 0
    for nd in comp:
        off[nd] = n
        n += nv[nd] + 1
    # undirected spanning tree from comp[0]
    adj = {nd: [] for nd in comp}
    for ei, (a, b, src, tgt) in enumerate(cedges):
        adj[a].append((ei, b))
        adj[b].append((ei, a))
    seen, tree, q = {comp[0]}, set(), [comp[0]]
    while q:
        a = q.pop()
        for ei, b in adj[a]:
            if b not in seen:
                seen.add(b)
                tree.add(ei)
                q.append(b)
    mats = []
    for ei, (a, b, src, tgt) in enumerate(cedges):
        m = max([C.tbound(e[1]) for e in src + tgt] + [0])
        Ls = lin(src, nv[a], m)
        Lt = lin(tgt, nv[b], m)
        mats.append((a, b, Ls, Lt, m))

    def rows_for(ei, r):
        a, b, Ls, Lt, m = mats[ei]
        rows = []
        for i in range(m + 1):
            row = [Fr(0)] * n
            for k in range(nv[b] + 1):
                row[off[b] + k] += Lt[i][k]
            for k in range(nv[a] + 1):
                row[off[a] + k] -= r * Ls[i][k]
            rows.append(row)
        return rows

    base = []
    for ei in tree:
        base += rows_for(ei, Fr(1))
    W = rank_null(base, n)         # columns of X = W w
    if not W:
        return None
    rest = [ei for ei in range(len(cedges)) if ei not in tree]
    sols = []

    def kernel(Wc, ei, r):
        rows = rows_for(ei, r)
        Mw = matmul(rows, [list(col) for col in zip(*Wc)])     # rows x d
        K = rank_null(Mw, len(Wc))
        if not K:
            return None
        # new basis: Wc^T K
        return [[sum(Wc[d][i] * kv[d] for d in range(len(Wc))) for i in range(n)] for kv in K]

    def dfs(Wc, todo, depth):
        if len(sols) >= 4 or depth > 60:
            return
        if not todo:
            sols.append(Wc)
            return
        # pick the most constrained edge: fewest candidate ratios
        best = None
        for ei in todo:
            probe = [kernel(Wc, ei, r) for r in (Fr(1), Fr(7, 5), Fr(13, 11))]
            if all(p is not None and len(p) == len(Wc) for p in probe):
                # always satisfied: drop it
                best = (0, ei, [(None, Wc)])
                break
            if all(p is not None for p in probe):
                continue           # free: decide later
            opts = []
            for r in RCANDS:
                K = kernel(Wc, ei, r)
                if K is not None:
                    opts.append((r, K))
            if best is None or len(opts) < best[0]:
                best = (len(opts), ei, opts)
            if not opts:
                return
        if best is None:
            # all left are free: take the smallest ratio near 1 first
            ei = todo[0]
            best = (0, ei, [(r, kernel(Wc, ei, r)) for r in
                            sorted(RCANDS, key=lambda r: abs(math.log(r)))[:40]])
        _, ei, opts = best
        todo2 = [x for x in todo if x != ei]
        for r, K in opts:
            if K is None:
                continue
            dfs(K, todo2, depth + 1)

    dfs(W, rest, 0)
    out = []
    for Wc in sols:
        X = positive(Wc, comp, off, nv, n)
        if X is not None:
            out.append({nd: X[off[nd]:off[nd] + nv[nd] + 1] for nd in comp})
    return out


def positive(Wc, comp, off, nv, n):
    """a nonnegative X in span(Wc), every constant >= 1"""
    d = len(Wc)
    if d == 1:
        v = Wc[0]
        for sgn in (1, -1):
            X = [sgn * x for x in v]
            if all(x >= 0 for x in X) and all(X[off[nd]] > 0 for nd in comp):
                return X
        return None
    import numpy as np
    from scipy.optimize import linprog
    Wm = np.array([[float(x) for x in col] for col in Wc]).T      # n x d
    A, bnd = [], []
    for i in range(n):
        A.append(-Wm[i])
        bnd.append(0.0)
    for nd in comp:
        A.append(-Wm[off[nd]])
        bnd.append(-1.0)
    res = linprog(np.zeros(d), A_ub=np.array(A), b_ub=np.array(bnd), bounds=[(None, None)] * d)
    if not res.success:
        return None
    w = [Fr(x).limit_denominator(10 ** 6) for x in res.x]
    X = [sum(Wc[k][i] * w[k] for k in range(d)) for i in range(n)]
    if all(x >= 0 for x in X) and all(X[off[nd]] > 0 for nd in comp):
        return X
    return None


def eval_lin(Evec, exprs):
    """E(exprs) as an aexp-like (const, {p: coef}) with Fractions"""
    c = Evec[0]
    co = {}
    for k, e in enumerate(exprs):
        c += Evec[k + 1] * e[0]
        for p, a in e[1]:
            co[p] = co.get(p, 0) + Evec[k + 1] * a
    return c, co


def ratio(Es, Et):
    """Et = r * Es coefficient-wise; r or None"""
    cs, cos = Es
    ct, cot = Et
    keys = set(cos) | set(cot)
    r = None
    for x, y in [(cs, ct)] + [(cos.get(p, 0), cot.get(p, 0)) for p in keys]:
        if x == 0:
            if y != 0:
                return None
            continue
        if r is None:
            r = Fr(y) / Fr(x)
        elif Fr(y) / Fr(x) != r:
            return None
    return r


# ---------------------------------------------------------- per instr ----

def solve_instr(S, E, fired_of, nv, t, ells):
    """(level, E, V) per node for instruction t, and the prime l"""
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    quiet = [nd for nd in S if t not in fired_of(nd)]
    qs = set(quiet)
    edges = []
    for nd in quiet:
        for s, src, tgt, rho2, cands in E[nd]:
            for l2 in cands:
                n2 = (l2, rho2)
                if n2 in qs:
                    edges.append((nd, n2, src, tgt))
    succ = {nd: [] for nd in quiet}
    for a, b, _, _ in edges:
        succ[a].append(b)
    comps = sccs(quiet, succ)       # reverse topological: sinks first
    cid = {}
    for i, cmp_ in enumerate(comps):
        for nd in cmp_:
            cid[nd] = i
    level = {}
    for i, cmp_ in enumerate(comps):
        lv = 0
        for nd in cmp_:
            for b in succ[nd]:
                if cid[b] != i:
                    lv = max(lv, level[b] + 1)
        for nd in cmp_:
            level[nd] = lv
    for nd in quiet:
        level.setdefault(nd, 0)
    Eall = {nd: [Fr(1)] + [Fr(0)] * nv[nd] for nd in quiet}
    Vall = {nd: (0, [0] * nv[nd]) for nd in quiet}
    jall = {}
    ell_used = None
    for i, cmp_ in enumerate(comps):
        cedges = [e for e in edges if cid[e[0]] == i and cid[e[1]] == i]
        if not cedges:
            continue
        # 1. plain ranking (E = 1)
        trivial = {nd: [Fr(1)] + [Fr(0)] * nv[nd] for nd in cmp_}
        got = None
        r = fit_V(cmp_, cedges, nv, trivial, None, milp, LinearConstraint, Bounds, np)
        if r is not None:
            got = (trivial, r[0], r[1], None)
        else:
            cands = find_E(cmp_, cedges, nv) or []
            for Ec in cands:
                for l in ells:
                    r = fit_V(cmp_, cedges, nv, Ec, l, milp, LinearConstraint, Bounds, np)
                    if r is not None:
                        got = (r[2], r[0], r[1], l)
                        break
                if got:
                    break
        if got is None:
            return None
        Ec, V, jj, l = got
        if l is not None:
            if ell_used not in (None, l):
                return None
            ell_used = l
        for nd in cmp_:
            Eall[nd] = Ec[nd]
            Vall[nd] = V[nd]
        jall.update(jj)
    return dict(level=level, E=Eall, V=Vall, ell=ell_used or 2)


def fit_V(comp, cedges, nv, Ec, l, milp, LinearConstraint, Bounds, np):
    """potentials pi (E_i scaled by l^pi_i), binaries y_e (j_e >= 1), V;
    None if infeasible"""
    # ratios
    rs = []
    for a, b, src, tgt in cedges:
        r = ratio(eval_lin(Ec[a], src), eval_lin(Ec[b], tgt))
        if r is None or r <= 0:
            return None
        rs.append(r)
    if l is None:
        if any(r != 1 for r in rs):
            return None
        ve = [0] * len(rs)
    else:
        ve = [nu(l, r) for r in rs]
        # the unit part must be an l-unit: automatic for prime l
    idx, n = {}, 0
    for nd in comp:
        idx[nd] = n
        n += 1 + nv[nd]
    npi = len(comp) if l is not None else 0
    pio = {nd: n + k for k, nd in enumerate(comp)} if l is not None else {}
    n2 = n + npi
    ny = len(cedges) if l is not None else 0
    yo = n2
    ntot = n2 + ny
    BIG = 10 ** 5
    A, lo, hi = [], [], []
    for ei, (a, b, src, tgt) in enumerate(cedges):
        m = max([C.tbound(e[1]) for e in src + tgt] + [0])
        if l is not None:
            # delta = ve + pi_b - pi_a <= -y
            row = np.zeros(ntot)
            row[pio[b]] += 1
            row[pio[a]] -= 1
            row[yo + ei] += 1
            A.append(row)
            lo.append(-np.inf)
            hi.append(-ve[ei])
        # V_a(src) - V_b(tgt) >= 1 - BIG y  (constant), >= -BIG y (coefs)
        for p in range(-1, m):
            row = np.zeros(ntot)
            if p < 0:
                row[idx[a]] += 1
                row[idx[b]] -= 1
            for k in range(nv[a]):
                e = src[k]
                row[idx[a] + 1 + k] += e[0] if p < 0 else C.tcoef(p, e[1])
            for k in range(nv[b]):
                e = tgt[k]
                row[idx[b] + 1 + k] -= e[0] if p < 0 else C.tcoef(p, e[1])
            if l is not None:
                row[yo + ei] += BIG
            A.append(row)
            lo.append(1 if p < 0 else 0)
            hi.append(np.inf)
    ub = np.full(ntot, 10 ** 6, dtype=float)
    lb = np.zeros(ntot)
    for k in range(n2, ntot):
        ub[k] = 1
    for nd in comp:
        if l is not None:
            ub[pio[nd]] = 60
    c = np.ones(ntot)
    for k in range(n2, ntot):
        c[k] = 0
    res = milp(c=c, constraints=LinearConstraint(np.array(A), np.array(lo), np.array(hi)),
               integrality=np.ones(ntot), bounds=Bounds(lb, ub))
    if not res.success:
        return None
    x = np.round(res.x).astype(int)
    V = {nd: (int(x[idx[nd]]), [int(v) for v in x[idx[nd] + 1:idx[nd] + 1 + nv[nd]]])
         for nd in comp}
    Eo = {}
    for nd in comp:
        sc = (l ** int(x[pio[nd]])) if l is not None else 1
        Eo[nd] = [v * sc for v in Ec[nd]]
    # integerize E jointly (a common factor coprime to nothing matters: it
    # scales every E by the same number, ratios unchanged)
    den = 1
    for nd in comp:
        for v in Eo[nd]:
            den = den * Fr(v).denominator // math.gcd(den, Fr(v).denominator)
    Eo = {nd: [int(v * den) for v in Eo[nd]] for nd in comp}
    return V, {}, Eo


# ------------------------------------------------------------ checker ----

def gcdl(xs, g=0):
    for x in xs:
        g = math.gcd(g, x)
    return g


def content(N, e):
    return gcdl([C.tcoef(k, e[1]) for k in range(N)], e[0])


def strip(l, A):
    j = 0
    while A > 0 and A % l == 0:
        A //= l
        j += 1
    return j, A


def nu_edge_ok(l, Esrc, Etgt, Vsrc, Vtgt):
    """TriNuTr.nu_edge: B e1 = A e2, gcd(B,l)=1, A = b l^j, gcd(b,l)=1,
    and (j >= 1 or V drops)"""
    e1 = Esrc
    e2 = Etgt
    N = max(C.tbound(e1[1]), C.tbound(e2[1]))
    g1, g2 = content(N, e1), content(N, e2)
    d = math.gcd(g1, g2)
    if d == 0:
        return False
    B, A = g2 // d, g1 // d
    j, b = strip(l, A)
    return (C.ale(C.ascale(B, e1), C.ascale(A, e2)) and C.ale(C.ascale(A, e2), C.ascale(B, e1))
            and math.gcd(B, l) == 1 and math.gcd(b, l) == 1
            and (j >= 1 or C.ale(C.aaddc(Vtgt, 1), Vsrc)))


def nu_check(cert, tabw, fired, nc):
    """TriNuTr.nlive_ok, transcribed"""
    P = nc['P']
    S = [(l, tuple(r)) for l, r in nc['S']]
    lvs = cert['leaves']
    if P <= 0:
        return 'P'
    rk = {tuple(t): d for t, d in nc['live']}
    for i, nd in enumerate(S):
        es = T.edges(cert, P, tabw, nd)
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
                        if t not in rk:
                            return 'no rank %s' % (t,)
                        l, rows = rk[t]
                        lv, Ev, Vv = rows[i] if i < len(rows) else (0, (1, []), (0, []))
                        lv2, Ev2, Vv2 = rows[i2] if i2 < len(rows) else (0, (1, []), (0, []))
                        if Ev[0] < 1 or Ev2[0] < 1 or l < 2:
                            return 'E const'
                        if lv2 < lv:
                            continue
                        if lv2 != lv:
                            return 'level up %s node %d' % (t, i)
                        e1 = C.veval(Ev, src)
                        e2 = C.veval(Ev2, tgt)
                        if not nu_edge_ok(l, e1, e2, C.veval(Vv, src), C.veval(Vv2, tgt)):
                            return 'edge %s node %d -> %d' % (t, i, i2)
    return None


# ---------------------------------------------------------------- main ----

def find_row(d, plist, ells):
    cert = T.detuple(dict(d['cert'], ranks=[], S=[], P=1))
    pins = set(map(tuple, cert['pins']))
    tabw = T.parse(d['spec'])
    if cert['mir']:
        tabw = T.mirror(tabw)
    tabw = {k: (None if k in pins else v) for k, v in tabw.items()}
    fired = [set(map(tuple, f)) for f in d['fired']]
    nv_of = lambda nd: cert['fams'][cert['leaves'][nd[0]]['f']]['n']
    errs = []
    for P in plist:
        try:
            S, E = closed_nodes(cert, P, tabw)
        except Fail as e:
            errs.append('P%d %s' % (P, e))
            continue
        nv = {nd: nv_of(nd) for nd in S}
        live = []
        ok = True
        for q in range(4):
            for h in range(2):
                t = (q, h)
                if t in pins:
                    continue
                r = solve_instr(S, E, lambda nd: fired[nd[0]], nv, t, ells)
                if r is None:
                    errs.append('P%d no nu-rank for %s' % (P, t))
                    ok = False
                    break
                rows = []
                for nd in S:
                    lvl = r['level'].get(nd, 0)
                    Ev = r['E'].get(nd, [1] + [0] * nv[nd])
                    Ev = (int(Ev[0]), [int(x) for x in Ev[1:]])
                    Vv = r['V'].get(nd, (0, [0] * nv[nd]))
                    rows.append((lvl, Ev, (int(Vv[0]), [int(x) for x in Vv[1]])))
                live.append((t, (r['ell'], rows)))
            if not ok:
                break
        if not ok:
            continue
        nc = dict(P=P, S=[(l, list(rho)) for l, rho in S], live=live)
        err = nu_check(cert, tabw, fired, nc)
        if err:
            errs.append('P%d check %s' % (P, err))
            continue
        out = dict(d['cert'])
        out.update(nc)
        out['spec'] = d['spec']
        return out
    return dict(spec=d['spec'], err='; '.join(errs))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('dump')
    ap.add_argument('out')
    ap.add_argument('--plist', default='1,2,3,4,6')
    ap.add_argument('--ells', default='2,3')
    ap.add_argument('--only', default=None)
    a = ap.parse_args()
    plist = [int(x) for x in a.plist.split(',')]
    ells = [int(x) for x in a.ells.split(',')]
    recs = {}
    for line in open(a.dump):
        d = json.loads(line)
        if d.get('verdict') == 'norank' and 'cert' in d:
            recs.setdefault(d['spec'], d)
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    n_ok = 0
    with open(a.out, 'a') as f:
        for spec, d in recs.items():
            if spec in done or (a.only and spec != a.only):
                continue
            try:
                r = find_row(d, plist, ells)
            except Exception as e:           # noqa: BLE001  (finder side only)
                r = dict(spec=spec, err='exception %r' % (e,))
            n_ok += 'err' not in r
            print(spec, 'OK P=%d' % r['P'] if 'err' not in r else r['err'][:150], flush=True)
            f.write(json.dumps(T.jsonable(r)) + '\n')
            f.flush()
    print('certified', n_ok)


if __name__ == '__main__':
    main()
