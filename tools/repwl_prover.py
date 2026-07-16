#!/usr/bin/env python3
"""Untrusted RepWL rank prover for neverqh_rwlrank certificates --
and the executable DESIGN SPEC for the planned Checkers/RepWL.v.

Abstract configuration (head-on-cell, sides symmetric):

    (q, hp, buf, litems, ritems)

  - buf: tuple of Sym cells, |buf| in {L, 2L, 3L} (whole blocks), the
    head at index hp;
  - litems/ritems: tuples of items (word, cnt, capped), NEAREST item
    first; a left word's cells are stored NEAREST-FIRST (mirror
    image), a right word's in tape order (nearest first) -- the two
    sides run the same code;
  - an item denotes word^cnt exactly if not capped, word^k for any
    k >= cnt if capped (cnt == T);
  - trailing blank infinity is implicit (a blank block folding into
    an empty list is absorbed).

Step (mirror of BBB/src/verify.c wg_succ, re-expressed symmetrically):
write at hp, move; if the head walks off the buffer: fold one block
from the departed end into that side's item list when |buf| = 3L
(merge into the nearest item if the word matches, count saturating
at T; blank block + empty list is absorbed), then pop the arrival
side's nearest item (blank block if the list is empty) and
materialize it; popping a capped item branches two ways (count was
exactly T -> cnt T-1 uncapped; count was > T -> item unchanged).

The rank procedure and measure vocabulary follow
BBB/docs/neverqh.md "RepWL ranking liveness": N/A, N/L, N/R
(nonblank counts, whole/left/right) and 0/l, 0/r (interior blank
counts) -- deltas are exact per node because both cap branches share
the physical step and witness bits never depend on capped counts.

Everything here is UNTRUSTED: the Coq checker re-derives the closure
and re-checks every edge; this module only has to FIND certificates.
"""

import sys
sys.setrecursionlimit(1000000)

MAX_ITEMS = 240
CAP_NODES = 400000


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


def sim_tape(tbl, t):
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
    return tape, pos, q


def rle(blocks, T):
    """Blocks (nearest-first) -> items with counts capped at T."""
    items = []
    for b in blocks:
        if items and items[-1][0] == b:
            w, c, cap = items[-1]
            if c < T:
                items[-1] = (w, c + 1, c + 1 == T)
            else:
                items[-1] = (w, T, True)
        else:
            items.append((b, 1, 1 == T))
    # strip the far-end blank-infinity blocks
    blank = tuple([0] * len(blocks[0])) if blocks else None
    while items and items[-1][0] == blank and not items[-1][2]:
        items.pop()
    return tuple(items)


def seed(tbl, L, T, t):
    """Abstract the configuration at step t: buffer = the L cells
    from the head rightward, sides blocked outward from it."""
    r = sim_tape(tbl, t)
    if r is None:
        return None
    tape, pos, q = r
    lo = min([pos] + list(tape))
    hi = max([pos] + list(tape))
    buf = tuple(tape.get(pos + i, 0) for i in range(L))
    lblocks = []
    p = pos - 1
    while p >= lo - L:
        lblocks.append(tuple(tape.get(p - i, 0) for i in range(L)))
        p -= L
    rblocks = []
    p = pos + L
    while p <= hi + L:
        rblocks.append(tuple(tape.get(p + i, 0) for i in range(L)))
        p += L
    return (q, 0, buf, rle(lblocks, T), rle(rblocks, T))


def push_item(items, word, T, blank):
    """Fold one departed block into a side list (nearest end)."""
    if not items:
        return (items if word == blank
                else ((word, 1, 1 == T),))
    w0, c0, cap0 = items[0]
    if w0 == word:
        c1 = min(c0 + 1, T)
        return ((w0, c1, c1 == T),) + items[1:]
    if len(items) >= MAX_ITEMS:
        return None
    return ((word, 1, 1 == T),) + items


def pop_item(items, T, blank):
    """Pop the nearest item: [(word, rest-items)] -- two entries on a
    cap branch."""
    if not items:
        return [(blank, items)]
    w0, c0, cap0 = items[0]
    if cap0:
        out = [(w0, items)]  # count was > T: unchanged
        if T - 1 >= 1:
            out.append((w0, ((w0, T - 1, False),) + items[1:]))
        else:
            out.append((w0, items[1:]))
        return out
    if c0 > 1:
        return [(w0, ((w0, c0 - 1, False),) + items[1:])]
    return [(w0, items[1:])]


def succs(tbl, L, T, a):
    """Abstract successors (1 or 2), or None on halt, or 'OVER'."""
    q, hp, buf, li, ri = a
    s = buf[hp]
    tr = tbl[(q, s)]
    if tr is None:
        return None
    w, d, q2 = tr
    buf = buf[:hp] + (w,) + buf[hp + 1:]
    hp += 1 if d == 'R' else -1
    if 0 <= hp < len(buf):
        return [(q2, hp, buf, li, ri)]
    blank = tuple([0] * L)
    side_right = hp >= 0
    if len(buf) == 3 * L:
        # fold the departed-end block
        if side_right:
            word = tuple(reversed(buf[:L]))  # left words nearest-first
            li2 = push_item(li, word, T, blank)
            if li2 is None:
                return 'OVER'
            buf = buf[L:]
            hp -= L
            li = li2
        else:
            word = buf[-L:]
            ri2 = push_item(ri, word, T, blank)
            if ri2 is None:
                return 'OVER'
            buf = buf[:-L]
            ri = ri2
    out = []
    if side_right:
        for word, ri2 in pop_item(ri, T, blank):
            out.append((q2, len(buf), buf + word, li, ri2))
    else:
        for word, li2 in pop_item(li, T, blank):
            out.append((q2, L - 1, tuple(reversed(word)) + buf, li2, ri))
    return out


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
        sl = succs(tbl, L, T, a)
        if sl is None or sl == 'OVER':
            return None
        todo.extend(sl)
    return a0, seen


# ---- measures: exact per-node deltas (docs/neverqh.md) ----

def zc(x):
    return 1 if x == 1 else 0


def side_nonblank_items(items):
    return any(any(c != 0 for c in w) for (w, _c, _cap) in items)


def arrival_info(tbl, L, a):
    """The arrival cell s2 and the nonblank-beyond bit, plus the
    departed-cell nonblank-beyond bit, for the step out of a."""
    q, hp, buf, li, ri = a
    s = buf[hp]
    w, d, _ = tbl[(q, s)]
    if d == 'R':
        if hp + 1 < len(buf):
            s2 = buf[hp + 1]
            nbb = any(zc(x) for x in buf[hp + 2:]) or side_nonblank_items(ri)
        elif not ri:
            s2, nbb = 0, 0
        else:
            w0, c0, cap0 = ri[0]
            s2 = w0[0]
            nb = any(zc(x) for x in w0[1:])
            if c0 >= 2 or cap0:
                nb = nb or any(zc(x) for x in w0)
            nbb = nb or side_nonblank_items(ri[1:])
        # departed cell = written w at old head; beyond = old left side
        dep_beyond = any(zc(x) for x in buf[:hp]) or side_nonblank_items(li)
        return s2, int(bool(nbb)), int(bool(dep_beyond))
    else:
        if hp - 1 >= 0:
            s2 = buf[hp - 1]
            nbb = any(zc(x) for x in buf[:hp - 1]) or side_nonblank_items(li)
        elif not li:
            s2, nbb = 0, 0
        else:
            w0, c0, cap0 = li[0]
            s2 = w0[0]  # left words nearest-first
            nb = any(zc(x) for x in w0[1:])
            if c0 >= 2 or cap0:
                nb = nb or any(zc(x) for x in w0)
            nbb = nb or side_nonblank_items(li[1:])
        dep_beyond = (any(zc(x) for x in buf[hp + 1:])
                      or side_nonblank_items(ri))
        return s2, int(bool(nbb)), int(bool(dep_beyond))


def rdelta(tbl, L, meas, a):
    """Per-node delta of measure meas in {'N/A','N/L','N/R','0/l','0/r'}."""
    q, hp, buf, li, ri = a
    s = buf[hp]
    w, d, _ = tbl[(q, s)]
    s2, nbb, depb = arrival_info(tbl, L, a)
    if meas == 'N/A':
        return zc(w) - zc(s)
    if meas == 'N/L':
        return zc(w) if d == 'R' else -zc(s2)
    if meas == 'N/R':
        return zc(w) if d == 'L' else -zc(s2)
    if meas == '0/l':
        if d == 'R':
            return (1 if (w == 0 and depb) else 0)
        return -(1 if (s2 == 0 and nbb) else 0)
    if meas == '0/r':
        if d == 'L':
            return (1 if (w == 0 and depb) else 0)
        return -(1 if (s2 == 0 and nbb) else 0)
    raise ValueError(meas)


ALL_MEAS = ['N/A', 'N/L', 'N/R', '0/l', '0/r']


def sccs(nodes, adj):
    import bulk_prover as bp
    return bp.sccs(nodes, adj)


def bellman(nodes, edges):
    import bulk_prover as bp
    return bp.bellman_potentials(nodes, edges)


def procedure(tbl, L, T, seen, adjmap, qq, cands):
    """Rules (a)/(b) over the q-avoiding graph; comps or None."""
    nodes = [a for a in seen if a[0] != qq]
    Kc = len(nodes) + 2
    alive = {}
    for a in nodes:
        for b in adjmap[a]:
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
                ds = {e: rdelta(tbl, L, m, e[0]) for e in intra}
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
                W = [(u, v, Kc * rdelta(tbl, L, m, u) + 1)
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
           t_cands=(0, 64, 256, 1024, 4096, 16384, 65536, 262144, 500000)):
    tbl = parse(mtext)
    for t in t_cands:
        r = build_closure(tbl, L, T, t)
        if r is None:
            continue
        a0, seen = r
        adjmap = {}
        bad = False
        for a in seen:
            sl = succs(tbl, L, T, a)
            if sl is None or sl == 'OVER':
                bad = True
                break
            adjmap[a] = sl
        if bad:
            continue
        states = sorted({a[0] for a in seen})
        comps_by_state = {}
        ok = True
        for qq in states:
            cands = list(dict.fromkeys(per_state.get(qq, []) + ALL_MEAS))
            comps = procedure(tbl, L, T, seen, adjmap, qq, cands)
            if comps is None:
                ok = False
                break
            comps_by_state[qq] = comps
        if ok:
            return {"t": t, "nseen": len(seen), "comps": comps_by_state}
    return None
