#!/usr/bin/env python3
"""NGramHist pilot: history-augmented n-gram closure + liveness over the
BBB4 residue.  UNTRUSTED prototype (matches mxdys' NGramCPS impl1 algorithm,
alphabet-generic via the xset falling-edge trick), plus a BBB4-style
never-QH liveness pass (per-state acyclicity of the q-avoiding subgraph over
the finite closed set).

Semantics fixed to BBB4:
  states A,B,C,D ; symbols 0,1 ; dirs L,R ; start state A, blank tape (0).
  machine string: A0 A1 B0 B1 C0 C1 D0 D1, each '<w><dir><state>' or '---'.
  augmented machine TM_history(k): cell = (bit, hist), hist = tuple of last-k
  (state,read) records; on step at (s,(i0,i1)) with tm[s][i0]=(o,d,s'):
  write (o, tuple(((s,i0),)+i1)[:k]), move d, goto s'.  (mxdys TM.v:1239)
"""
import sys, collections

# ---------- machine decode ----------
def decode(mstr):
    """census string -> tm[state][bit] = (write_bit, dir 'L'/'R', next_state) or None."""
    groups = mstr.strip().split('_')
    assert len(groups) == 4, mstr
    tm = {}
    for si, g in enumerate(groups):
        st = "ABCD"[si]
        tm[st] = {}
        for bit in (0, 1):
            cell = g[bit*3:bit*3+3]
            if cell == '---':
                tm[st][bit] = None
            else:
                w = int(cell[0]); d = cell[1]; nx = cell[2]
                tm[st][bit] = (w, d, nx)
    return tm

# ---------- augmented step function ----------
# A symbol is either a plain bit (0/1) [k=0 / plain] or an HSym tuple
# (bit, hist) where hist is a tuple of (state,bit) pairs, len<=k.
def make_step(tm, k):
    """Return (step_fn, blank_sym).  step_fn(state, sym)-> (nxt,dir,write_sym) | None."""
    if k == 0:
        blank = 0
        def step(s, sym):
            tr = tm[s][sym]
            if tr is None: return None
            w, d, nx = tr
            return (nx, d, w)
        return step, blank
    blank = (0, ())
    def step(s, sym):
        i0, i1 = sym
        tr = tm[s][i0]
        if tr is None: return None
        w, d, nx = tr
        newhist = ((s, i0),) + i1
        newhist = newhist[:k]
        return (nx, d, (w, newhist))
    return step, blank

def symbit(sym):
    return sym if isinstance(sym, int) else sym[0]

# ---------- concrete augmented-tape simulation (to seed past the transient) ----------
def simulate(tm, k, t):
    """Run the augmented machine k-history from blank for t steps.
    Return ('config', state, L, head, R) with L,R nearest-first lists over the
    augmented alphabet, or ('halt', step) if it halts first."""
    step, blank = make_step(tm, k)
    # tape as dicts left[i]=cell at head-1-i (nearest first), right[j]=head+1+j
    left = {}; right = {}; head = blank; s = 'A'
    def get(d, i): return d.get(i, blank)
    for _ in range(t):
        tr = step(s, head)
        if tr is None:
            return ('halt',)
        nx, dr, w = tr
        if dr == 'R':
            # write w at head; head moves right: new head = right[0]; left gets w
            # shift left up by one (index i -> i+1), left[0]=w
            nl = {0: w}
            for i, v in left.items(): nl[i+1] = v
            left = nl
            head = get(right, 0)
            nr = {}
            for j, v in right.items():
                if j >= 1: nr[j-1] = v
            right = nr
        else:
            nr = {0: w}
            for j, v in right.items(): nr[j+1] = v
            right = nr
            head = get(left, 0)
            nl = {}
            for i, v in left.items():
                if i >= 1: nl[i-1] = v
            left = nl
        s = nx
    Lmax = (max(left) if left else -1)
    Rmax = (max(right) if right else -1)
    L = [get(left, i) for i in range(Lmax+1)]
    R = [get(right, j) for j in range(Rmax+1)]
    return ('config', s, L, head, R, blank)

def seed_from_config(cfg, len_l, len_r):
    """Return (seed_midword, lset, rset) seeding all depth>=1 windows of the
    step-t config's half-tapes (BBB4 ng_seed_side)."""
    _, s, L, head, R, blank = cfg
    def win(lst, d, n):
        return tuple(lst[d+i] if d+i < len(lst) else blank for i in range(n))
    lw = win(L, 0, len_l); rw = win(R, 0, len_r)
    lset = {}; rset = {}
    # depth d = 1 .. len+1 (blank beyond)
    for d in range(1, len(L) + 2):
        xset_ins(lset, win(L, d, len_l))
    for d in range(1, len(R) + 2):
        xset_ins(rset, win(R, d, len_r))
    seed = (lw, rw, head, s)
    return seed, lset, rset

# ---------- n-gram closure (mxdys MidWord/xset, alphabet-generic) ----------
# MidWord = (tuple l, tuple r, m, s):  l,r nearest-first windows of the
# augmented alphabet, length len_l/len_r; m = head sym; s = state.
# lset/rset : dict prefix(tuple of len-1) -> set of completing far symbols.
def xset_ins(xs, gram):
    pre = gram[:-1]; last = gram[-1]
    xs.setdefault(pre, set()).add(last)
def xset_get(xs, pre):
    return xs.get(pre, ())

def close(step, blank, len_l, len_r, gas, rounds=4000, seed=None, lset=None, rset=None):
    """Return dict: closed(bool), midwords(set), edges(dict mw->list mw),
    reason, nctx.  A closed halt-free set => NonHalt.
    If seed/lset/rset given, seed from there (past-transient); else from blank."""
    if seed is None:
        l0 = (blank,)*len_l
        r0 = (blank,)*len_r
        lset = {}; rset = {}
        xset_ins(lset, l0); xset_ins(rset, r0)
        seed = (l0, r0, blank, 'A')
    else:
        lset = dict((k, set(v)) for k, v in lset.items())
        rset = dict((k, set(v)) for k, v in rset.items())
    for rnd in range(rounds):
        # explore reachable MidWords under fixed sets; collect donations
        mset = set([seed]); todo = [seed]; edges = {}
        halted = False; steps = 0
        new_l = []; new_r = []
        while todo:
            steps += 1
            if steps > gas:
                return dict(closed=False, reason='gas', midwords=mset, edges=edges,
                            nctx=len(mset))
            mw = todo.pop()
            l, r, m, s = mw
            tr = step(s, m)
            if tr is None:
                return dict(closed=False, reason='halt', midwords=mset, edges=edges,
                            nctx=len(mset))
            nx, d, w = tr
            succs = []
            if d == 'R':
                new_l.append(l)                    # donate left gram to lset
                # branch far-right cell
                pre = r[1:]                         # deeper right (len-1)
                for x in xset_get(rset, pre):
                    nl = (w,) + l[:-1]
                    nr = r[1:] + (x,)
                    nm = r[0]
                    nmw = (nl, nr, nm, nx)
                    succs.append(nmw)
            else:  # 'L'
                new_r.append(r)                    # donate right gram to rset
                pre = l[1:]
                for x in xset_get(lset, pre):
                    nr = (w,) + r[:-1]
                    nl = l[1:] + (x,)
                    nm = l[0]
                    nmw = (nl, nr, nm, nx)
                    succs.append(nmw)
            edges[mw] = succs
            for nmw in succs:
                if nmw not in mset:
                    mset.add(nmw); todo.append(nmw)
        # grow sets with donations
        before = (sum(len(v) for v in lset.values()), sum(len(v) for v in rset.values()))
        for g in new_l: xset_ins(lset, g)
        for g in new_r: xset_ins(rset, g)
        after = (sum(len(v) for v in lset.values()), sum(len(v) for v in rset.values()))
        if after == before:
            # fixpoint: verify closed = every explored succ was in mset (it is,
            # since we added them) and no halt/gas -> closed.
            return dict(closed=True, reason='fixpoint', midwords=mset, edges=edges,
                        nctx=len(mset))
    return dict(closed=False, reason='rounds', midwords=set(), edges={}, nctx=0)

# ---------- liveness: per-state acyclicity of q-avoiding subgraph ----------
def _acyclic_avoiding(mset, edges, q):
    """True iff the subgraph on nodes with state != q is acyclic."""
    nodes = [mw for mw in mset if mw[3] != q]
    nodeset = set(nodes)
    adj = {mw: [t for t in edges.get(mw, ()) if t in nodeset] for mw in nodes}
    color = {}
    for start in nodes:
        if color.get(start): continue
        stack = [(start, iter(adj[start]))]; color[start] = 1
        while stack:
            node, it = stack[-1]; advanced = False
            for nb in it:
                c = color.get(nb, 0)
                if c == 1: return False
                if c == 0:
                    color[nb] = 1; stack.append((nb, iter(adj[nb]))); advanced = True; break
            if not advanced:
                color[node] = 2; stack.pop()
    return True

def liveness_state(res, sentinel='__none__'):
    """Acyclicity of the subgraph avoiding `sentinel` (full graph if no node
    has that state)."""
    if not res['closed']: return False
    return _acyclic_avoiding(res['midwords'], res['edges'], sentinel)

def _zc(sym): return 1 if symbit(sym) == 1 else 0

def _ngm_delta(tm, meas, mw):
    """BBB4 ngm_delta for the count-of-1s measures, over the augmented node.
    meas in {'All','Left','Right'}.  Reads the bit (fst) of augmented syms."""
    l, r, m, s = mw
    tr = tm[s][symbit(m)]
    if tr is None: return 0
    w, d, nx = tr
    zw = 1 if w == 1 else 0
    zs = _zc(m)
    if meas == 'All': return zw - zs
    if meas == 'Left':
        return zw if d == 'R' else -_zc(l[0])
    if meas == 'Right':
        return (-_zc(r[0])) if d == 'R' else zw
    return 0

def _no_positive_cycle(nodes, adj, w):
    """True iff the weighted digraph (nodes, adj with weight w(a,b)) has no
    cycle of total weight > 0 (Bellman-Ford longest-path; proxy for a lex
    measure being non-increasing around every cycle)."""
    d = {n: 0 for n in nodes}
    N = len(nodes)
    for it in range(N + 1):
        changed = False
        for a in nodes:
            da = d[a]
            for b in adj[a]:
                nw = da + w(a, b)
                if nw > d[b]:
                    d[b] = nw; changed = True
                    if it == N:  # relaxed after N rounds => positive cycle
                        return False
        if not changed:
            return True
    return True

def _lex_measure_discharges(tm, mset, edges, q):
    """Some count measure m has no positive q-avoiding cycle (=> lex-
    dischargeable with m primary; the residual zero-cycles fall to a lex
    tie-breaker)."""
    nodes = [mw for mw in mset if mw[3] != q]
    nodeset = set(nodes)
    adj = {mw: [t for t in edges.get(mw, ()) if t in nodeset] for mw in nodes}
    for meas in ('Left', 'Right', 'All'):
        wf = lambda a, b, meas=meas: _ngm_delta(tm, meas, a)
        if _no_positive_cycle(nodes, adj, wf):
            return meas
    return None

def _node_dir(step, mw):
    l, r, m, s = mw
    tr = step(s, m)
    return None if tr is None else tr[1]

def _has_nonblank(win):
    return any(symbit(x) == 1 for x in win)

def _runner_avoiding(step, mset, q):
    """BBB4 runner/fuel gate: exists a dir d s.t. every q-avoiding node steps d
    AND has a nonblank ahead in direction d (fuel).  => q recurs."""
    for d, wi in (('R', 1), ('L', 0)):   # R-> inspect right window (idx1); L-> left(idx0)
        ok = True
        for mw in mset:
            if mw[3] == q: continue
            if _node_dir(step, mw) != d: ok = False; break
            win = mw[wi]  # 0=left window, 1=right window
            if not _has_nonblank(win): ok = False; break
        if ok: return True
    return False

def _tarjan_scc(mset, edges):
    """Return list of SCCs (each a set of nodes)."""
    index = {}; low = {}; onstk = {}; stk = []; sccs = []; idx = [0]
    nodes = list(mset)
    sys.setrecursionlimit(1 << 20)
    for root in nodes:
        if root in index: continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = idx[0]; idx[0] += 1
                stk.append(v); onstk[v] = True
            recurse = False
            succs = edges.get(v, ())
            i = pi
            while i < len(succs):
                w = succs[i]
                if w not in mset:
                    i += 1; continue
                if w not in index:
                    work[-1] = (v, i+1); work.append((w, 0)); recurse = True; break
                elif onstk.get(w):
                    low[v] = min(low[v], index[w])
                i += 1
            if recurse: continue
            if low[v] == index[v]:
                comp = set()
                while True:
                    w = stk.pop(); onstk[w] = False; comp.add(w)
                    if w == v: break
                sccs.append(comp)
            work.pop()
            if work:
                p = work[-1][0]; low[p] = min(low[p], low[v])
    return sccs

def recurrent_states(res):
    """States that appear in a recurrent SCC (non-singleton, or singleton with
    self-loop) => recur in the abstraction (SCC upper-bound proxy)."""
    if not res['closed']: return set()
    mset = res['midwords']; edges = res['edges']
    sccs = _tarjan_scc(mset, edges)
    rec = set()
    for comp in sccs:
        cyclic = len(comp) > 1 or any(
            (mw in comp) for mw in comp for t in edges.get(mw, ()) if t == mw)
        if cyclic:
            for mw in comp: rec.add(mw[3])
    return rec

def liveness(res, step=None, tm=None):
    """For each appearing state q: rank(acyclic) OR runner(fuel) OR
    lex-count-measure gate.  Returns (all_pass, per dict, appearing, gate dict)."""
    if not res['closed']:
        return (False, {}, set(), {})
    mset = res['midwords']; edges = res['edges']
    appearing = set(mw[3] for mw in mset)
    per = {}; gate = {}
    for q in appearing:
        if _acyclic_avoiding(mset, edges, q):
            per[q] = True; gate[q] = 'rank'; continue
        if step and _runner_avoiding(step, mset, q):
            per[q] = True; gate[q] = 'runner'; continue
        m = _lex_measure_discharges(tm, mset, edges, q) if tm else None
        if m:
            per[q] = True; gate[q] = 'lex-' + m
        else:
            per[q] = False; gate[q] = 'FAIL'
    return (all(per.values()), per, appearing, gate)

# ---------- driver ----------
def visited_states_prefix(tm, k, t):
    """States visited in steps [0,t) from blank (for the never-QH obligation:
    a transient-only state also demands the liveness gate)."""
    step, blank = make_step(tm, k)
    left = {}; right = {}; head = blank; s = 'A'; vis = set()
    for _ in range(t):
        vis.add(s)
        tr = step(s, head)
        if tr is None: break
        nx, dr, w = tr
        if dr == 'R':
            nl = {0: w}
            for i, v in left.items(): nl[i+1] = v
            left = nl; head = right.get(0, blank)
            right = {j-1: v for j, v in right.items() if j >= 1}
        else:
            nr = {0: w}
            for j, v in right.items(): nr[j+1] = v
            right = nr; head = left.get(0, blank)
            left = {i-1: v for i, v in left.items() if i >= 1}
        s = nx
    vis.add(s)
    return vis

def analyze(mstr, k, len_l, len_r, gas, t=0):
    tm = decode(mstr)
    step, blank = make_step(tm, k)
    if t == 0:
        res = close(step, blank, len_l, len_r, gas)
        prefix_vis = set()
    else:
        cfg = simulate(tm, k, t)
        if cfg[0] == 'halt':
            return dict(closed=False, reason='halt-prefix', nctx=0, live_all=False,
                        per={}, appearing=set(), n_appear=0, n_live=0, boarded=False)
        seed, lset, rset = seed_from_config(cfg, len_l, len_r)
        res = close(step, blank, len_l, len_r, gas, seed=seed, lset=lset, rset=rset)
        prefix_vis = visited_states_prefix(tm, k, t)
    live_all, per, appearing, gate = liveness(res, step=step, tm=tm)
    obliged = (prefix_vis | appearing) if res['closed'] else set()
    rec = recurrent_states(res) if res['closed'] else set()
    boarded = False
    if res['closed']:
        ok = True
        for q in obliged:
            if q in per:
                if not per[q]: ok = False; break
            else:  # transient-only state: needs full-closure acyclicity
                if not _acyclic_avoiding(res['midwords'], res['edges'], '__none__'):
                    ok = False; break
        boarded = ok
    # SCC upper-bound: all obliged states appear in a recurrent SCC
    scc_ok = res['closed'] and obliged.issubset(rec)
    return dict(closed=res['closed'], reason=res['reason'], nctx=res['nctx'],
                live_all=live_all, per=per, appearing=appearing, gate=gate,
                n_appear=len(appearing), n_live=sum(1 for v in per.values() if v),
                boarded=boarded, obliged=obliged, scc_ok=scc_ok, rec=rec)

if __name__ == '__main__':
    # self-test: sweep t (seed past transient) for plain and hist2g2
    for m in sys.argv[1:]:
        print(m)
        for (tag,k,ll,rr,gas) in [('plain-2',0,2,2,20000),('hist2g2',2,2,2,40000)]:
            best=None
            for t in (0,20,60,150,400):
                r = analyze(m,k,ll,rr,gas,t=t)
                mark = 'BOARD' if r.get('boarded') else ('close' if r['closed'] else '-')
                sccm = 'sccOK' if r.get('scc_ok') else ''
                print(f"  {tag:8s} t={t:4d} closed={r['closed']!s:5s}({r['reason']:11s}) "
                      f"nctx={r['nctx']:5d} appear={r['n_appear']} rank+run={r['n_live']}/{r['n_appear']} "
                      f"{mark} {sccm}")
                if r.get('boarded'): best=t; break
