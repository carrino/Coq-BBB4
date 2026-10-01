#!/usr/bin/env python3
"""BLC5: block lists whose rare instruction fires only at the list's
OVERFLOW (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC5).

    python3 tools/closeouttr/blc5/lx5.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 400]
    python3 tools/closeouttr/blc5/lx5.py batch OUT.jsonl --tag BLC5 [--chunk 6]

The exploration is BLC4's (blc4/learn4.py learns the language, blc4/lg4.py
explores), unchanged.  What is new is the liveness, checked by
theories/Counters/ListGlueLexTr.v (lgx_check):

  * per instruction, first ListGlue2Tr's item-additive ranking (the MILP of
    lg_batch.l_live_search);
  * if there is none, a LEXICOGRAPHIC rank read from the list's far end
    (`lex_search`): per node a list of constant window entries W, per side
    one constant weight per tail transition (the right side global, the left
    side per node), so that on every non-firing step the sequence
      rev(hi tail weights) ++ W ++ (lo tail weights)
    drops lexicographically or stays equal; the steps where it may stay equal
    get the additive ranking V (the same MILP on those steps only).  The
    window entry count per node is the potential that keeps the sequence's
    length constant (|unfolded| + |W| = |folded| + |W'| on every step).
    One MILP with 0/1 "equal so far" variables per middle position decides
    which steps are strict; it maximises the strict ones.

`c_xlive_ok` replays ListGlueLexTr.xlive_ok exactly before a certificate is
written.
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
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc4'))
import learn4 as L4                                 # noqa: E402
import lg3                                          # noqa: E402
import lg4                                          # noqa: E402
import lg_batch as G                                # noqa: E402
import ti_batch as T                                # noqa: E402
import ti_coq as C                                  # noqa: E402

KMAX = int(os.environ.get('LX5_K', '3'))           # largest entry value
INSTRS = [(q, h) for q in range(4) for h in range(2)]


# ------------------------------------------------------------ the graph ----

def node_graph(c, P):
    """TriGlue's (leaf, residue) nodes reachable from the boot node, and
    per node the edges of lg_batch.l_edges"""
    b = G.l_boot_node(c, P)
    if b is None:
        return None
    S = [b]
    seen = {b}
    E = {}
    k = 0
    while k < len(S):
        nd = S[k]
        k += 1
        es = G.l_edges(c, P, nd)
        if es is None:
            return None
        E[nd] = es
        for e in es:
            for l2 in e[7]:
                n2 = (l2, e[6])
                if n2 not in seen:
                    seen.add(n2)
                    S.append(n2)
        if len(S) > 6000:
            return None
    return S, E


def t_edges(S, E, fired, t):
    """the non-firing steps for t, grouped by (src, tgt, unfolded and folded
    transitions)"""
    out = collections.OrderedDict()
    for nd in S:
        if t in fired[nd[0]]:
            continue
        for (src, tgt, uL, uR, fL, fR, rho2, cands) in E[nd]:
            for l2 in cands:
                if t in fired[l2]:
                    continue
                key = (nd, (l2, rho2), tuple(x for x, _ in uL), tuple(x for x, _ in uR),
                       tuple(x for x, _ in fL), tuple(x for x, _ in fR))
                out.setdefault(key, []).append((src, tgt, uL, uR, fL, fR))
    return out


# ------------------------------------------------------------- MILP glue ----

class MILP:
    def __init__(self):
        self.n = 0
        self.rows = []
        self.lo = []
        self.hi = []
        self.ub = []

    def var(self, ub):
        self.n += 1
        self.ub.append(ub)
        return self.n - 1

    def add(self, lin, lo=None, hi=None):
        self.rows.append(lin)
        self.lo.append(lo)
        self.hi.append(hi)

    def solve(self, cost, tl=300):
        import numpy as np
        from scipy.optimize import milp, LinearConstraint, Bounds
        from scipy.sparse import lil_matrix
        A = lil_matrix((max(1, len(self.rows)), self.n))
        for i, r in enumerate(self.rows):
            for v, x in r.items():
                A[i, v] += x
        lo = np.array([-np.inf if x is None else x for x in self.lo] or [-np.inf], dtype=float)
        hi = np.array([np.inf if x is None else x for x in self.hi] or [np.inf], dtype=float)
        c = np.zeros(self.n)
        for v, x in cost.items():
            c[v] += x
        res = milp(c=c, constraints=LinearConstraint(A.tocsr(), lo, hi),
                   integrality=np.ones(self.n), bounds=Bounds(0, np.array(self.ub, dtype=float)),
                   options=dict(time_limit=tl))
        if res.x is None:
            return None
        return [int(round(v)) for v in res.x]


def lin(*pairs):
    d = {}
    for v, k in pairs:
        d[v] = d.get(v, 0) + k
    return d


# ---------------------------------------------------- additive ranking ----

def v_search(c, S, steps):
    """ListGlue2Tr's additive ranking (window affine, default tail weights
    bL / bR per node) on the given steps: {node: ((c, coefs), bL, bR)}"""
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    nv = {nd: c['fams'][c['leaves'][nd[0]]['f']]['n'] for nd in S}
    off = {}
    n = 0
    for nd in S:
        off[nd] = n
        n += 3 + nv[nd]
    A, lo = [], []
    for (nd, n2, src, tgt, uL, uR, fL, fR) in steps:
        o, o2 = off[nd], off[n2]
        m1, m2 = nv[nd], nv[n2]
        params = sorted(set(p for e in src + tgt for p, _ in e[1]))
        row = np.zeros(n)
        row[o] += 1
        row[o2] -= 1
        for kk, e in enumerate(src[:m1]):
            row[o + 1 + kk] += e[0]
        for kk, e in enumerate(tgt[:m2]):
            row[o2 + 1 + kk] -= e[0]
        row[o + 1 + m1] += len(uL)
        row[o + 2 + m1] += len(uR)
        row[o2 + 1 + m2] -= len(fL)
        row[o2 + 2 + m2] -= len(fR)
        A.append(row)
        lo.append(1)
        for p_ in params:
            row = np.zeros(n)
            for kk, e in enumerate(src[:m1]):
                row[o + 1 + kk] += C.tcoef(p_, e[1])
            for kk, e in enumerate(tgt[:m2]):
                row[o2 + 1 + kk] -= C.tcoef(p_, e[1])
            A.append(row)
            lo.append(0)
        for dd in (1, 2):
            row = np.zeros(n)
            row[o + dd + m1] += 1
            row[o2 + dd + m2] -= 1
            A.append(row)
            lo.append(0)
    if not A:
        return {nd: ((0, [0] * nv[nd]), 0, 0) for nd in S}
    A = np.array(A)
    res = milp(c=np.ones(n), constraints=LinearConstraint(A, np.array(lo), np.inf),
               integrality=np.ones(n), bounds=Bounds(0, 10 ** 6), options=dict(time_limit=300))
    if res.x is None:
        return None
    x = np.round(res.x).astype(int)
    if (A @ x < np.array(lo)).any():
        return None
    return {nd: ((int(x[off[nd]]), [int(y) for y in x[off[nd] + 1:off[nd] + 1 + nv[nd]]]),
                 int(x[off[nd] + 1 + nv[nd]]), int(x[off[nd] + 2 + nv[nd]])) for nd in S}


def all_steps(edges):
    return [(k[0], k[1]) + tuple(x) for k, xs in edges.items() for x in xs]


# ------------------------------------------------------- the lex search ----

def lex_search(c, S, edges, msd, K=KMAX):
    """the constant-slot lexicographic rank (see the module doc); msd True:
    the far end is on the right"""
    if not edges:
        return None
    ell = entry_counts(c, S, edges)
    if ell is None:
        return None
    ell, m = ell
    ltr = [i for i, tr in enumerate(c['trans']) if tr['left']]
    rtr = [i for i, tr in enumerate(c['trans']) if not tr['left']]
    mp = MILP()
    W = {nd: [mp.var(K) for _ in range(m[nd])] for nd in S}
    if msd:
        dH = {tr: mp.var(K) for tr in rtr}
        dLo = {(nd, tr): mp.var(K) for nd in S for tr in ltr}
        lo_tr = ltr
    else:
        dH = {tr: mp.var(K) for tr in ltr}
        dLo = {(nd, tr): mp.var(K) for nd in S for tr in rtr}
        lo_tr = rtr

    def mid(nd, IL, IR):
        hi, lo = (IR, IL) if msd else (IL, IR)
        return ([dH[x] for x in reversed(hi) if ell[x]] + W[nd]
                + [dLo[(nd, x)] for x in lo if ell[x]])
    cost = {}
    ens = []
    for key in edges:
        a, b, uL, uR, fL, fR = key
        Ms = mid(a, uL, uR)
        Mt = mid(b, fL, fR)
        if len(Ms) != len(Mt):
            return None
        n = len(Ms)
        es = [mp.var(1) for _ in range(n + 1)]
        mp.add({es[0]: 1}, 1, 1)
        for p in range(n):
            mp.add(lin((es[p + 1], 1), (es[p], -1)), hi=0)
            if Ms[p] == Mt[p]:
                mp.add(lin((es[p + 1], 1), (es[p], -1)), lo=0)
                continue
            d = [(Ms[p], 1), (Mt[p], -1)]
            mp.add(lin(*d, (es[p], -1 - (K + 1)), (es[p + 1], 1)), lo=-(K + 1))
            mp.add(lin(*d, (es[p + 1], K)), hi=K)
        en = es[n]
        for tr in lo_tr:
            mp.add(lin((dLo[(b, tr)], 1), (dLo[(a, tr)], -1), (en, K)), hi=K)
        cost[en] = cost.get(en, 0) + 1
        ens.append((key, en))
    x = mp.solve(cost)
    if x is None:
        return None
    eq = [key for key, en in ens if x[en] == 1]
    steps = [(k[0], k[1]) + tuple(s) for k in eq for s in edges[k]]
    V = v_search(c, S, steps)
    if V is None:
        return None
    hiv = {tr: x[v] for tr, v in dH.items()}
    lov = {k: x[v] for k, v in dLo.items()}
    ntr = len(c['trans'])
    lx = []
    for nd in S:
        hw = [[(0, hiv[tr])] if tr in hiv and ell[tr] else [] for tr in range(ntr)]
        lw = [[(0, lov[(nd, tr)])] if (nd, tr) in lov and ell[tr] else [] for tr in range(ntr)]
        wL, wR = (lw, hw) if msd else (hw, lw)
        lx.append(dict(W=[(x[v], []) for v in W[nd]], wL=wL, bL=0, wR=wR, bR=0))
    return dict(msd=msd, lx=lx, V=[V[nd] for nd in S], nstrict=len(ens) - len(eq), nsteps=len(ens))


def entry_counts(c, S, edges):
    """per transition 0 or 1 sequence entries (most of them 1), and per node
    the window entry count, so that every step keeps the sequence length:
    |W(src)| + entries(unfolded) = |W(tgt)| + entries(folded)"""
    ntr = len(c['trans'])
    mp = MILP()
    ell = [mp.var(1) for _ in range(ntr)]
    m = {nd: mp.var(30) for nd in S}
    for (a, b, uL, uR, fL, fR) in edges:
        d = collections.Counter()
        d[m[a]] += 1
        d[m[b]] -= 1
        for x in uL + uR:
            d[ell[x]] += 1
        for x in fL + fR:
            d[ell[x]] -= 1
        d = {k: v for k, v in d.items() if v}
        if d:
            mp.add(d, 0, 0)
    cost = {v: -100 for v in ell}
    for v in m.values():
        cost[v] = 1
    x = mp.solve(cost)
    if x is None:
        return None
    return [x[v] for v in ell], {nd: x[v] for nd, v in m.items()}


def live_search(c, fired, P):
    """per instruction an additive ranking, else a lexicographic one"""
    g = node_graph(c, P)
    if g is None:
        return 'graph'
    S, E = g
    ranks, lex = [], []
    for t in INSTRS:
        if t in c['pins']:
            continue
        edges = t_edges(S, E, fired, t)
        if not edges:
            continue
        V = v_search(c, S, all_steps(edges))
        if V is not None:
            ranks.append((t, [V[nd] for nd in S]))
            continue
        r = None
        for msd in (True, False):
            r = lex_search(c, S, edges, msd)
            if r is not None:
                break
        if r is None:
            return ('norank', t)
        ranks.append((t, r['V']))
        lex.append((t, r['msd'], r['lx']))
    return dict(P=P, S=[(l, list(rho)) for l, rho in S],
                ranks=[(t, [dict(V=v[0], bL=v[1], bR=v[2]) for v in Vs]) for t, Vs in ranks],
                lex=lex)


# ------------------------------------------------------------ replica ----

def xget(w, b, t):
    return w[t] if t < len(w) else [(0, b)]


def c_xwle(w1, b1, w2, b2):
    if b1 > b2:
        return False
    for k in range(max(len(w1), len(w2))):
        x1, x2 = xget(w1, b1, k), xget(w2, b2, k)
        if len(x1) != len(x2) or any(p[0] > q[0] or p[1] > q[1] for p, q in zip(x1, x2)):
            return False
    return True


def c_xwshape(w1, b1, w2, b2):
    return all(len(xget(w1, b1, k)) == len(xget(w2, b2, k)) for k in range(max(len(w1), len(w2))))


def wenta(w, b, te):
    return [C.aaddc(C.ascale(a, te[1]), bb) for a, bb in xget(w, b, te[0])]


def mida(msd, x, xs, IL, IR):
    if msd:
        hw, hb, lw, lb, hi, lo = x['wR'], x['bR'], x['wL'], x['bL'], IR, IL
    else:
        hw, hb, lw, lb, hi, lo = x['wL'], x['bL'], x['wR'], x['bR'], IL, IR
    return ([y for te in hi for y in wenta(hw, hb, te)][::-1] + [C.veval(v, xs) for v in x['W']]
            + [y for te in lo for y in wenta(lw, lb, te)])


def lexchk(l1, l2):
    if len(l1) != len(l2):
        return None
    for x1, x2 in zip(l1, l2):
        if C.ale(C.aaddc(x1, 1), x2):
            return True
        if not C.ale(x1, x2):
            return None
    return False


def c_twa(w, b, I):
    """ListGlue2Tr.twa with an empty weight list"""
    acc = (0, ())
    for _ in I:
        acc = C.aadd(acc, (b, ()))
    return acc


LX0 = dict(W=[], wL=[], bL=0, wR=[], bR=0)


def c_xlive_ok(cert, fired):
    """ListGlueLexTr.xlive_ok, replayed (ranks with empty weight lists, as
    ListGlue2Tr's renderer writes them)"""
    P = cert['P']
    if P <= 0:
        return 'P'
    S = [(l, tuple(r)) for l, r in cert['S']]
    sidx = {nd: i for i, nd in enumerate(S)}
    rk = dict((tuple(t), V) for t, V in cert['ranks'])
    lx = dict((tuple(t), (msd, xs)) for t, msd, xs in cert.get('lex', []))
    z0 = dict(V=(0, []), bL=0, bR=0)
    for i, nd in enumerate(S):
        if nd[0] >= len(cert['leaves']):
            return 'node leaf'
        es = G.l_edges(cert, P, nd)
        if es is None:
            return 'pdiv'
        for (src, tgt, uL, uR, fL, fR, rho2, cands) in es:
            for l2 in cands:
                i2 = sidx.get((l2, rho2))
                if i2 is None:
                    return 'not closed'
                for t in INSTRS:
                    if t in cert['pins'] or t in fired[nd[0]] or t in fired[l2]:
                        continue
                    Vs = rk.get(t, [])
                    r = Vs[i] if i < len(Vs) else z0
                    r2 = Vs[i2] if i2 < len(Vs) else z0
                    lhs = C.aaddc(C.aadd(C.veval(r2['V'], tgt),
                                         C.aadd(c_twa([], r2['bL'], fL), c_twa([], r2['bR'], fR))), 1)
                    rhs = C.aadd(C.veval(r['V'], src), C.aadd(c_twa([], r['bL'], uL), c_twa([], r['bR'], uR)))
                    vok = C.ale(lhs, rhs) and r2['bL'] <= r['bL'] and r2['bR'] <= r['bR']
                    if t not in lx:
                        if not vok:
                            return 'rank %s at node %d' % (t, i)
                        continue
                    msd, xs = lx[t]
                    x = xs[i] if i < len(xs) else LX0
                    x2 = xs[i2] if i2 < len(xs) else LX0
                    Ms = mida(msd, x, src, uL, uR)
                    Mt = mida(msd, x2, tgt, fL, fR)
                    hk = ('wR', 'bR') if msd else ('wL', 'bL')
                    lk = ('wL', 'bL') if msd else ('wR', 'bR')
                    if (len(Ms) != len(Mt) or not c_xwle(x2[hk[0]], x2[hk[1]], x[hk[0]], x[hk[1]])
                            or not c_xwshape(x2[lk[0]], x2[lk[1]], x[lk[0]], x[lk[1]])):
                        return 'lex len/hi %s at node %d' % (t, i)
                    r3 = lexchk(Mt, Ms)
                    if r3 is None:
                        return 'lex %s at node %d' % (t, i)
                    if r3 is False and not (c_xwle(x2[lk[0]], x2[lk[1]], x[lk[0]], x[lk[1]]) and vok):
                        return 'lex eq %s at node %d' % (t, i)
    return None


def c_checkx(cert, tab):
    tabw = {k: (None if k in cert['pins'] else v) for k, v in tab.items()}
    if not G.c_mins_ok(cert):
        return 'mins'
    if not lg3.c_maxs_ok(cert):
        return 'maxs'
    err = G.c_fams_ok(cert, tabw)
    if err:
        return 'fams: ' + err
    fired = [G.leaf_fired(tabw, lf) for lf in cert['leaves']]
    err = c_xlive_ok(cert, fired)
    if err:
        return 'live: ' + err
    err = G.c_boot_ok(cert, tab, tabw)
    if err:
        return err
    b = G.l_boot_node(cert, cert['P'])
    if b is None or (b[0], list(b[1])) not in [(l, list(r)) for l, r in cert['S']]:
        return 'boot node'
    return None


# ------------------------------------------------------------- render ----

def r_lx(x):
    def w(ws):
        return '[' + ';'.join('[' + ';'.join('(%d,%d)' % tuple(p) for p in e) + ']' for e in ws) + ']'
    return '(mkLx [%s] %s %d %s %d)' % (
        ';'.join('(%d,[%s])' % (v[0], ';'.join(str(y) for y in v[1])) for v in x['W']),
        w(x['wL']), x['bL'], w(x['wR']), x['bR'])


def renderx(c):
    s = lg3.render2(c)
    head = 'apply coversTr_nqh, ('
    assert s.startswith(head)
    body = s[len(head):]
    lemma = 'lg2_sound_mirror' if c.get('mir') else 'lg2_sound'
    assert body.startswith(lemma + ' _\n      ')
    tail = '.\n  vm_cast_no_check (eq_refl true).'
    assert body.endswith(')' + tail)
    base = body[len(lemma + ' _\n      '):-len(')' + tail)]
    lex = '[' + ';\n      '.join('((%s,%s), (%s, [%s]))' % (
        G.ST[t[0]], G.SYM[t[1]], G.r_bool(msd), ';'.join(r_lx(x) for x in xs))
        for t, msd, xs in c.get('lex', [])) + ']'
    lemx = 'lgx_sound_mirror' if c.get('mir') else 'lgx_sound'
    return '%s%s _\n      (mkLCX %s\n      %s))%s' % (head, lemx, base, lex, tail)


# --------------------------------------------------------------- find ----

def find_dir(spec, lang, t0, mir=False, plist=G.PLIST):
    X, pins, boot = lg4.explore_row(spec, lang, t0, mir)
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    cert = lg3.assemble2(X, X.t0, pins)
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
        lv = live_search(cert, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = c_checkx(cert, tab)
            if err:
                return dict(err='check: ' + err)
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


def find_row(spec, t0s=(20000, 100000)):
    lang, mir, info = L4.learn(spec)
    errs = []
    if info.get('tboot') and info['tboot'] > 20000:
        t0s = (info['tboot'],) + tuple(t for t in t0s if t < info['tboot'])
    for t0 in t0s:
        try:
            r = find_dir(spec, lang, t0, mir=mir)
        except T.Fail as e:
            r = dict(err=str(e))
        if 'err' not in r:
            r['spec'] = spec
            r['learn'] = info
            return r
        errs.append('t%d %s' % (t0, r['err']))
    return dict(spec=spec, err=' / '.join(errs), learn=info)


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0):
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    try:
        return find_row(spec)
    except T.Fail as e:
        return dict(spec=spec, err=str(e))
    except Timeout:
        return dict(spec=spec, err='timeout')
    except RecursionError:
        return dict(spec=spec, err='recursion')
    finally:
        if timeout:
            signal.alarm(0)


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    L4.L3.lsnap_bin()
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(G.jsonable(r)) + '\n')
            f.flush()
            stats['ok' if 'err' not in r else 'fail'] += 1
            print(r['spec'], r.get('err', 'OK')[:200], flush=True)
    print(dict(stats))


def detuplex(c):
    c = G.detuple(c)
    c['lex'] = [(tuple(t), msd, xs) for t, msd, xs in c.get('lex', [])]
    return c


def cmd_batch(a):
    from cbt import next_free, write_batch
    rem = T.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(detuplex(c))
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], renderx(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr '
                                            'ListGlueLexTr.'],
                                entries, 'block-list rows whose rare instruction fires at the '
                                         'overflow: the far-end lexicographic liveness '
                                         '(ListGlueLexTr, lgx_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, T.REPO) for p in made)))


def main():
    if os.environ.get('PYTHONHASHSEED') != '0':
        os.environ['PYTHONHASHSEED'] = '0'
        os.execv(sys.executable, [sys.executable] + sys.argv)
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=400)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='BLC5')
    p.add_argument('--chunk', type=int, default=6)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
