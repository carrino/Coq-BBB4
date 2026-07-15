"""Untrusted bulk prover for neverqh_rank / neverqh_ngram certificates.

Reimplements the BBB harness's n-gram closure construction and
ranking-liveness procedure (rules (a)/(b), src/quietngram.c) with the
FULL pattern-measure vocabulary of the C verifier's rkv_delta
(src/verify.c): a measure is a nonblank-containing word over {0,1}
counted over the whole tape ('A') or strictly left/right of the head
('L'/'R'), with window-coverage constraints len <= n+1 for 'A' and
len <= n-1 for 'L'/'R'.

Everything here is UNTRUSTED: the output certificate tables are
re-verified inside Coq by ngram_check_neverqh_lex.  This module only
has to *find* certificates, not to be right.
"""

import sys
sys.setrecursionlimit(1000000)


def parse(m):
    tbl = {}
    for qi, part in enumerate(m.split('_')):
        for si in range(2):
            e = part[3*si:3*si+3]
            tbl[(qi, si)] = None if e == '---' else (int(e[0]), e[1], ord(e[2]) - 65)
    return tbl


def build_closure(tbl, n, t, cap=200000):
    """Simulate t steps, seed gram sets from the reached config, then
    grow the sets to a fixpoint (the C prover's two-level loop).
    Returns (seen, lset, rset) or None."""
    tape = {}
    pos = 0
    q = 0
    for _ in range(t):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
    minp = min([pos] + list(tape))
    maxp = max([pos] + list(tape))
    Lf = lambda i: tape.get(pos - 1 - i, 0)
    Rf = lambda i: tape.get(pos + 1 + i, 0)
    win = lambda f, d: tuple(f(d + i) for i in range(n))
    depth = max(pos - minp, maxp - pos) + n + 2
    lset = {win(Lf, d) for d in range(1, depth)}
    rset = {win(Rf, d) for d in range(1, depth)}
    a0 = (q, tape.get(pos, 0), win(Lf, 0), win(Rf, 0))
    for rounds in range(1, 401):
        seen = set()
        todo = [a0]
        while todo:
            a = todo.pop()
            if a in seen:
                continue
            seen.add(a)
            if len(seen) > cap:
                return None
            q1, s1, lw, rw = a
            tr = tbl[(q1, s1)]
            if tr is None:
                continue
            w, d, q2 = tr
            if d == 'R':
                for x in (0, 1):
                    rw2 = rw[1:] + (x,)
                    if rw2 in rset:
                        todo.append((q2, rw[0], (w,) + lw[:-1], rw2))
            else:
                for x in (0, 1):
                    lw2 = lw[1:] + (x,)
                    if lw2 in lset:
                        todo.append((q2, lw[0], lw2, (w,) + rw[:-1]))
        newl = {a[2] for a in seen if tbl[(a[0], a[1])] and tbl[(a[0], a[1])][1] == 'R'}
        newr = {a[3] for a in seen if tbl[(a[0], a[1])] and tbl[(a[0], a[1])][1] == 'L'}
        if newl <= lset and newr <= rset:
            if any(tbl[(a[0], a[1])] is None for a in seen):
                return None
            return seen, lset, rset, a0, rounds
        lset |= newl
        rset |= newr
    return None


def succs(tbl, lset, rset, seen, a):
    q1, s1, lw, rw = a
    w, d, q2 = tbl[(q1, s1)]
    out = []
    if d == 'R':
        for x in (0, 1):
            rw2 = rw[1:] + (x,)
            b = (q2, rw[0], (w,) + lw[:-1], rw2)
            if rw2 in rset and b in seen:
                out.append(b)
    else:
        for x in (0, 1):
            lw2 = lw[1:] + (x,)
            b = (q2, lw[0], lw2, (w,) + rw[:-1])
            if lw2 in lset and b in seen:
                out.append(b)
    return out


def occ(patt, xs):
    """Occurrences of patt fully inside xs (mirrors Coq occ)."""
    plen = len(patt)
    return sum(1 for i in range(len(xs)) if tuple(xs[i:i + plen]) == patt)


def pdelta(tbl, n, patt, reg, a):
    """Exact per-edge delta of the (patt, reg) measure, mirroring the
    Coq pm_delta EXACTLY (theories/Checkers/NGram.v): region 'A' is
    the count difference over the 2|p|-1 window around the head;
    'L'/'R' are prefix-occurrence indicators at the half-tape edit."""
    q1, s1, lw, rw = a
    w, d, _ = tbl[(q1, s1)]
    plen = len(patt)
    p1 = plen - 1
    if reg == 'A':
        mid = tuple(reversed(lw[:p1]))
        return (occ(patt, mid + (w,) + tuple(rw[:p1]))
                - occ(patt, mid + (s1,) + tuple(rw[:p1])))
    if reg == 'L':
        rp = tuple(reversed(patt))
        if d == 'R':
            return 1 if rp == (w,) + tuple(lw[:p1]) else 0
        return -(1 if rp == tuple(lw[:plen]) else 0)
    else:
        if d == 'R':
            return -(1 if patt == tuple(rw[:plen]) else 0)
        return 1 if patt == (w,) + tuple(rw[:p1]) else 0


def meas_ok(patt, reg, n):
    """The Coq pm_ok constraint (finiteness: the pattern must contain
    a nonblank; window coverage: |p|-1 <= n for 'A', |p| <= n else)."""
    if 1 not in patt:
        return False
    return (len(patt) - 1 <= n) if reg == 'A' else (len(patt) <= n)


def sccs(nodes, adj):
    idx = {}
    low = {}
    onstk = {}
    stk = []
    out = []
    c = [0]
    for s in nodes:
        if s in idx:
            continue
        work = [(s, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                idx[v] = low[v] = c[0]
                c[0] += 1
                stk.append(v)
                onstk[v] = True
            recurse = False
            ns = adj(v)
            for i in range(pi, len(ns)):
                u = ns[i]
                if u not in idx:
                    work[-1] = (v, i + 1)
                    work.append((u, 0))
                    recurse = True
                    break
                elif onstk.get(u):
                    low[v] = min(low[v], idx[u])
            if recurse:
                continue
            if low[v] == idx[v]:
                comp = []
                while True:
                    u = stk.pop()
                    onstk[u] = False
                    comp.append(u)
                    if u == v:
                        break
                out.append(comp)
            work.pop()
            if work:
                p = work[-1][0]
                low[p] = min(low[p], low[v])
    return out


def bellman_potentials(nodes, edges):
    """Feasible potentials phi with W(e) <= phi[u] - phi[v] for each
    edge, or None if some cycle has positive W-sum (Bellman-Ford)."""
    dist = {v: 0 for v in nodes}
    for _ in range(len(nodes) + 1):
        ch = False
        for (u, v, We) in edges:
            if dist[u] - We < dist[v]:
                dist[v] = dist[u] - We
                ch = True
        if not ch:
            mn = min(dist.values())
            return {v: int(dist[v] - mn) for v in nodes}
    return None


def procedure(tbl, n, seen, lset, rset, qq, cands):
    """Reduce the q-avoiding context graph with rules (a)/(b) over the
    candidate measures, emitting lexicographic components; None on
    failure.  cands: list of (patt, reg) pairs, coverage-checked."""
    nodes = [a for a in seen if a[0] != qq]
    Kc = len(nodes) + 2
    alive = {}
    for a in nodes:
        for b in succs(tbl, lset, rset, seen, a):
            if b[0] != qq:
                alive[(a, b)] = True
    comps = []
    rounds = 0
    while True:
        rounds += 1
        if rounds > 200:
            return None
        adjmap = {}
        for (u, v) in alive:
            adjmap.setdefault(u, []).append(v)
        adj = lambda v: adjmap.get(v, [])
        comp_list = sccs(nodes, adj)
        cyclic = [c for c in comp_list
                  if len(c) > 1 or c[0] in adjmap.get(c[0], [])]
        if not cyclic:
            rank = {v: 0 for v in nodes}
            for _ in range(len(nodes) + 1):
                ch = False
                for (u, v) in alive:
                    if rank[u] < rank[v] + 1:
                        rank[u] = rank[v] + 1
                        ch = True
                if not ch:
                    break
            comps.append(("rank", rank))
            return comps
        cidx = {}
        for i, c in enumerate(comp_list):
            for v in c:
                cidx[v] = i
        crank = {i: 0 for i in range(len(comp_list))}
        for _ in range(len(comp_list) + 1):
            ch = False
            for (u, v) in alive:
                if cidx[u] != cidx[v] and crank[cidx[u]] < crank[cidx[v]] + 1:
                    crank[cidx[u]] = crank[cidx[v]] + 1
                    ch = True
            if not ch:
                break
        comps.append(("rank", {v: crank[cidx[v]] for v in nodes}))
        progress = False
        for c in cyclic:
            cs = set(c)
            intra = [(u, v) for (u, v) in alive if u in cs and v in cs]
            done = False
            for (patt, reg) in cands:
                ds = {e: pdelta(tbl, n, patt, reg, e[0]) for e in intra}
                if all(d <= 0 for d in ds.values()) and any(d < 0 for d in ds.values()):
                    comps.append(("meas", patt, reg, 1, {v: 0 for v in c}, cs))
                    for e in intra:
                        if ds[e] < 0:
                            del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            for (patt, reg) in cands:
                W = [(u, v, Kc * pdelta(tbl, n, patt, reg, u) + 1) for (u, v) in intra]
                phi = bellman_potentials(list(cs), W)
                if phi is not None:
                    comps.append(("meas", patt, reg, Kc, phi, cs))
                    for e in intra:
                        del alive[e]
                    progress = True
                    break
        if not progress:
            return None


def lex_check(tbl, n, seen, lset, rset, qq, comps):
    """Re-check every q-avoiding edge against the emitted components
    (the same decision procedure the Coq engine's lex_ok runs)."""
    for a in seen:
        if a[0] == qq:
            continue
        for b in succs(tbl, lset, rset, seen, a):
            if b[0] == qq:
                continue
            good = False
            for comp in comps:
                if comp[0] == "rank":
                    r = comp[1]
                    if r.get(b, 0) < r.get(a, 0):
                        good = True
                        break
                    if r.get(b, 0) <= r.get(a, 0):
                        continue
                    break
                else:
                    _, patt, reg, K, phi, gate = comp
                    d = pdelta(tbl, n, patt, reg, a)
                    ga = a in gate
                    gb = b in gate
                    if ga and gb:
                        v = K * d + phi.get(b, 0) - phi.get(a, 0)
                        if v <= -1:
                            good = True
                            break
                        if v <= 0:
                            continue
                        break
                    if not gb:
                        continue
                    break
            if not good:
                return False, (a, b)
    return True, None


def parse_cert_measures(path):
    """Extract machine text, n, and the per-state measure token lists
    from a BBB .cert file."""
    mtext = None
    n = None
    per_state = {}
    for line in open(path):
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "machine":
            mtext = parts[1]
        elif parts[0] == "ngram_n":
            n = int(parts[1])
        elif parts[0] == "rank_q":
            qi = ord(parts[1]) - 65
            toks = parts[3:]
            ms = []
            for tk in toks:
                patt_s, reg = tk.split('/')
                ms.append((tuple(int(ch) for ch in patt_s), reg.upper()))
            per_state[qi] = ms
    return mtext, n, per_state


DEFAULT_MEASURES = [((1,), 'A'), ((1,), 'L'), ((1,), 'R')]


def decide(mtext, n, per_state_measures, t_cands=(0, 64, 256, 1024, 4096,
                                                  16384, 65536, 262144, 500000)):
    """Try to certify machine mtext at window n: minimal t whose
    closure and per-state rank procedure all succeed.  Returns
    (t, seen, lset, rset, comps_by_state) or None."""
    tbl = parse(mtext)
    for t in t_cands:
        r = build_closure(tbl, n, t)
        if r is None:
            continue
        seen, lset, rset, _a0, rounds = r
        comps_by_state = {}
        allok = True
        for qq in sorted({a[0] for a in seen}):
            cands = list(dict.fromkeys(
                [m for m in per_state_measures.get(qq, []) if meas_ok(m[0], m[1], n)]
                + [m for m in DEFAULT_MEASURES if meas_ok(m[0], m[1], n)]))
            comps = procedure(tbl, n, seen, lset, rset, qq, cands)
            if comps is None:
                allok = False
                break
            ok, _bad = lex_check(tbl, n, seen, lset, rset, qq, comps)
            if not ok:
                allok = False
                break
            comps_by_state[qq] = comps
        if allok:
            return t, seen, lset, rset, comps_by_state, rounds
    return None
