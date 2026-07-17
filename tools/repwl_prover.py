#!/usr/bin/env python3
"""Untrusted RepWL rank prover for neverqh_rwlrank certificates --
the exact Python mirror of theories/Checkers/RepWL.v.

Abstract configuration, mirroring the Coq [rconf] shape:

    (q, li, lb, h, rb, ri)

with [lb]/[rb] the buffer cells nearest-first around the head and
[li]/[ri] the item lists (word, cnt, capped), nearest item first,
left words stored nearest-first (mirror image).  The step, the seed
(ctape-list chunk + right-fold rle), the encoding, and the component
semantics (comp_strict/comp_noninc/lex_edge_ok over the five
measures) all mirror the Coq definitions bit for bit, so a
certificate found here verifies under [rw_check_neverqh_sound].

Everything here is UNTRUSTED: the Coq checker re-derives the closure
and re-checks every edge; this module only has to FIND certificates.
"""

import sys
sys.setrecursionlimit(1000000)

CAP_NODES = 400000

MEAS = ['N/A', 'N/L', 'N/R', '0/l', '0/r']


def parse(m):
    tbl = {}
    for qi, part in enumerate(m.split('_')):
        for si in range(2):
            e = part[3 * si:3 * si + 3]
            tbl[(qi, si)] = (None if e == '---'
                             else (int(e[0]), e[1], ord(e[2]) - 65))
    return tbl


def parse_cert(path):
    mtext = None
    L = T = None
    per_state = {}
    for line in open(path):
        p = line.split()
        if not p:
            continue
        if p[0] == "machine":
            mtext = p[1]
        elif p[0] == "block":
            L = int(p[1])
        elif p[0] == "threshold":
            T = int(p[1])
        elif p[0] == "rank_q":
            per_state[ord(p[1]) - 65] = p[3:]
    return mtext, L, T, per_state


# ---- ctape simulation (mirror of CTape.csteps) ----

def csteps(tbl, t):
    """t steps from ([],0,[]); returns (q, l, h, r) as lists, or None
    on halt.  Mirrors cstep/ctape_move."""
    q, l, h, r = 0, [], 0, []
    for _ in range(t):
        tr = tbl[(q, h)]
        if tr is None:
            return None
        w, d, q2 = tr
        if d == 'R':
            l = [w] + l
            h = r[0] if r else 0
            r = r[1:]
        else:
            h2 = l[0] if l else 0
            l = l[1:]
            r = [w] + r
            h = h2
        q = q2
    return q, l, h, r


# ---- seed (mirror of chunk_go / rle / rw_seed) ----

def padw(L, w):
    return tuple(w) + (0,) * (L - len(w))


def chunk(L, l):
    out = []
    l = list(l)
    while l:
        out.append(padw(L, l[:L]))
        l = l[L:]
    return out


def rle(T, blocks):
    """Right fold: process the far end first (mirror of Coq rle)."""
    out = []
    for b in reversed(blocks):
        if not out:
            if all(x == 0 for x in b):
                continue
            out = [(b, 1, 1 == T)]
        else:
            w0, c0, cap0 = out[0]
            if w0 == b:
                c1 = min(c0 + 1, T)
                out[0] = (w0, c1, cap0 or c1 == T)
            else:
                out.insert(0, (b, 1, 1 == T))
    return tuple(out)


def seed(tbl, L, T, t):
    cs = csteps(tbl, t)
    if cs is None:
        return None
    q, l, h, r = cs
    return (q, rle(T, chunk(L, l)), (), h,
            padw(L - 1, r[:L - 1]), rle(T, chunk(L, r[L - 1:])))


# ---- the step (mirror of push_item / pop_item / rw_succs) ----

def word_blank(w):
    return all(x == 0 for x in w)


def push_item(T, w, items):
    if not items:
        return () if word_blank(w) else ((w, 1, 1 == T),)
    w0, c0, cap0 = items[0]
    if w0 == w:
        c1 = min(c0 + 1, T)
        return ((w0, c1, cap0 or c1 == T),) + items[1:]
    return ((w, 1, 1 == T),) + items


def pop_item(L, items):
    """None = fail closed (zero count / empty word)."""
    if not items:
        return [(tuple([0] * L), ())]
    w0, c0, cap0 = items[0]
    if not w0 or c0 == 0:
        return None
    dec = items[1:] if c0 == 1 else ((w0, c0 - 1, False),) + items[1:]
    if cap0:
        return [(w0, items), (w0, dec)]
    return [(w0, dec)]


def rw_succs(tbl, L, T, a):
    """Successor list, or None on halt/fail-closed."""
    q, li, lb, h, rb, ri = a
    tr = tbl[(q, h)]
    if tr is None:
        return None
    w, d, q2 = tr
    if d == 'R':
        if rb:
            return [(q2, li, (w,) + lb, rb[0], rb[1:], ri)]
        lb1 = (w,) + lb
        if 3 * L <= len(lb1):
            lb2 = lb1[:2 * L]
            li2 = push_item(T, lb1[2 * L:], li)
        else:
            lb2, li2 = lb1, li
        ps = pop_item(L, ri)
        if ps is None:
            return None
        return [(q2, li2, lb2, wd[0], wd[1:], ri2) for wd, ri2 in ps]
    else:
        if lb:
            return [(q2, li, lb[1:], lb[0], (w,) + rb, ri)]
        rb1 = (w,) + rb
        if 3 * L <= len(rb1):
            rb2 = rb1[:2 * L]
            ri2 = push_item(T, rb1[2 * L:], ri)
        else:
            rb2, ri2 = rb1, ri
        ps = pop_item(L, li)
        if ps is None:
            return None
        return [(q2, li2, wd[1:], wd[0], rb2, ri2) for wd, li2 in ps]


def build_closure(tbl, L, T, t, cap=CAP_NODES):
    a0 = seed(tbl, L, T, t)
    if a0 is None:
        return None
    seen = set()
    todo = [a0]
    while todo:
        a = todo.pop()
        if a in seen:
            continue
        seen.add(a)
        if len(seen) > cap:
            return None
        sl = rw_succs(tbl, L, T, a)
        if sl is None:
            return None
        todo.extend(sl)
    return a0, seen


# ---- encoding (mirror of rconf_enc) ----

def syms_app(l, p):
    p = 2 * p
    for x in reversed(l):
        p = 2 * (2 * p + x) + 1
    return p


def nat_app(n, p):
    p = 2 * p
    for _ in range(n):
        p = 2 * p + 1
    return p


def bool_app(b, p):
    return 2 * p + (1 if b else 0)


def item_app(it, p):
    w, c, cap = it
    return syms_app(w, nat_app(c, bool_app(cap, p)))


def items_app(items, p):
    p = 2 * p
    for it in reversed(items):
        p = 2 * item_app(it, p) + 1
    return p


ST_TAG = {0: 0, 1: 1, 2: 2, 3: 3}


def st_app(q, p):
    return 4 * p + q


def rconf_enc(a):
    q, li, lb, h, rb, ri = a
    p = items_app(ri, 1)
    p = items_app(li, p)
    p = syms_app(rb, p)
    p = syms_app(lb, p)
    p = 2 * p + h
    return st_app(q, p)


# ---- measures (mirror of arr_s2 / arr_nbb / dep_nbb / rw_delta) ----

def items_nb(items):
    return any(not word_blank(w) for (w, _c, _cap) in items)


def arr_s2(b, items):
    if b:
        return b[0]
    if items:
        w = items[0][0]
        return w[0] if w else 0
    return 0


def arr_nbb(b, items):
    if b:
        return (not word_blank(b[1:])) or items_nb(items)
    if not items:
        return False
    w, c, cap = items[0]
    return ((not word_blank(w[1:]))
            or ((c >= 2 or cap) and not word_blank(w))
            or items_nb(items[1:]))


def dep_nbb(b, items):
    return (not word_blank(b)) or items_nb(items)


def rw_delta(tbl, m, a):
    q, li, lb, h, rb, ri = a
    w, d, _ = tbl[(q, h)]
    if m == 'N/A':
        return w - h
    if m == 'N/L':
        return w if d == 'R' else -arr_s2(lb, li)
    if m == 'N/R':
        return w if d == 'L' else -arr_s2(rb, ri)
    if m == '0/l':
        if d == 'R':
            return 1 if (w == 0 and dep_nbb(lb, li)) else 0
        return -(1 if (arr_s2(lb, li) == 0 and arr_nbb(lb, li)) else 0)
    if m == '0/r':
        if d == 'L':
            return 1 if (w == 0 and dep_nbb(rb, ri)) else 0
        return -(1 if (arr_s2(rb, ri) == 0 and arr_nbb(rb, ri)) else 0)
    raise ValueError(m)


# ---- component semantics (mirror of comp_strict / comp_noninc) ----
# comps: ("rank", {a: v}) | ("meas", m, K, {a: v}, gateset)

def comp_strict(tbl, comp, fa, fb):
    if comp[0] == "rank":
        r = comp[1]
        return r.get(fb, 0) < r.get(fa, 0)
    _, m, K, phi, gate = comp
    if fa not in gate or fb not in gate:
        return False
    return K * rw_delta(tbl, m, fa) + phi.get(fb, 0) - phi.get(fa, 0) <= -1


def comp_noninc(tbl, comp, fa, fb):
    if comp[0] == "rank":
        r = comp[1]
        return r.get(fb, 0) <= r.get(fa, 0)
    _, m, K, phi, gate = comp
    if fb not in gate:
        return True
    if fa not in gate:
        return False
    return K * rw_delta(tbl, m, fa) + phi.get(fb, 0) - phi.get(fa, 0) <= 0


def lex_edge_ok(tbl, comps, fa, fb):
    for comp in comps:
        if comp_strict(tbl, comp, fa, fb):
            return True
        if not comp_noninc(tbl, comp, fa, fb):
            return False
    return False


def warmup_states(tbl, t):
    q, l, h, r = 0, [], 0, []
    out = set()
    for _ in range(t):
        out.add(q)
        w, d, q2 = tbl[(q, h)]
        if d == 'R':
            l, h, r = [w] + l, (r[0] if r else 0), r[1:]
        else:
            l, h, r = l[1:], (l[0] if l else 0), [w] + r
        q = q2
    return out


def lex_check(tbl, adj, seen, qq, comps):
    """Mirror of the engine's lex_ok over the q-avoiding graph."""
    for fa in seen:
        if fa[0] == qq:
            continue
        for fb in adj[fa]:
            if fb[0] == qq:
                continue
            if not lex_edge_ok(tbl, comps, fa, fb):
                return False
    return True


def sccs(nodes, adjf):
    import bulk_prover as bp
    return bp.sccs(nodes, adjf)


def bellman(nodes, edges):
    import bulk_prover as bp
    return bp.bellman_potentials(nodes, edges)


def procedure(tbl, seen, adj, qq, cands):
    """Rules (a)/(b) over the q-avoiding graph; comps or None."""
    nodes = [a for a in seen if a[0] != qq]
    Kc = len(nodes) + 2
    alive = {}
    for a in nodes:
        for b in adj[a]:
            if b[0] != qq:
                alive[(a, b)] = True
    comps = []
    for _ in range(300):
        am = {}
        for (u, v) in alive:
            am.setdefault(u, []).append(v)
        comp_list = sccs(nodes, lambda v: am.get(v, []))
        cyclic = [c for c in comp_list
                  if len(c) > 1 or c[0] in am.get(c[0], [])]
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
            for m in cands:
                ds = {e: rw_delta(tbl, m, e[0]) for e in intra}
                if (all(x <= 0 for x in ds.values())
                        and any(x < 0 for x in ds.values())):
                    comps.append(("meas", m, 1, {v: 0 for v in c}, cs))
                    for e in intra:
                        if ds[e] < 0:
                            del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            for m in cands:
                W = [(u, v, Kc * rw_delta(tbl, m, u) + 1)
                     for (u, v) in intra]
                phi = bellman(list(cs), W)
                if phi is not None:
                    comps.append(("meas", m, Kc, phi, cs))
                    for e in intra:
                        del alive[e]
                    progress = True
                    break
        if not progress:
            return None
    return None


def decide(mtext, L, T, per_state,
           t_cands=(0, 64, 256, 1024, 4096, 16384, 65536)):
    tbl = parse(mtext)
    for t in t_cands:
        r = build_closure(tbl, L, T, t)
        if r is None:
            continue
        a0, seen = r
        adj = {a: rw_succs(tbl, L, T, a) for a in seen}
        states = sorted({a[0] for a in seen} | warmup_states(tbl, t))
        comps_by_state = {}
        ok = True
        for qq in states:
            cands = list(dict.fromkeys(per_state.get(qq, []) + MEAS))
            comps = procedure(tbl, seen, adj, qq, cands)
            if comps is None or not lex_check(tbl, adj, seen, qq, comps):
                ok = False
                break
            comps_by_state[qq] = comps
        if ok:
            return {"t": t, "nseen": len(seen), "a0": a0,
                    "comps": comps_by_state}
    return None
