#!/usr/bin/env python3
"""UNTRUSTED: nested arms -- a chain of chains -- for [Checkers/LadderNest.v].

An arm whose carry costs time QUADRATIC in the run it carries has no
[LadderKernel] chain: every chain step costs [ca*j + cb].  Measured on the
rows SCOPING_INSTR 7.4.CE2 filed as "quadratic-cost carry", the carry is a
loop of ROUNDS, each an ordinary kernel rule whose cost is affine in its own
index (the run it sweeps), and the number of rounds is affine in the arm's
index.  [LadderNest] states exactly that as a SEGMENT program:

    NCh chain                      a kernel chain (base steps)
    NUp k AL AR i0 al be rl rr fin al*j+be rounds of inner rule k, index
                                   upwards from i0, each consuming AL / AR
    NDn k BL BR i0 al be rl rr fin al*j+be rounds of inner rule k, index
                                   down to i0, each pushing BL / BR

This module mirrors the Coq side algebra ([sdep] .. [nrun]) verbatim and
SEARCHES for such a program: simulate the arm at a few concrete [j] with a
marker in every opaque tail, find the state/symbol the rounds pass through,
fit an UP or DOWN inner rule to consecutive visits, prove it with the
ordinary chain search ([lapcert.derive_chain], both tails opaque), fit the
round count across [j], and glue with chains before and after.

Nothing here carries proof weight: [LadderNest.check_narm] re-runs every
program in the kernel.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))
sys.path.insert(0, HERE)

import lapcert as LC                                              # noqa: E402

MARK = 9      # an opaque tail cell: reading it means the rule depends on X


# ------------------------------------------------ the Coq side algebra, mirrored

def sdep(s):
    return bool(s[1]) and s[2] != 0


def sflatl(s):
    pre, u, a, b, post = s
    return tuple(pre) + tuple(u) * b + tuple(post)


def scanon(s):
    return s if sdep(s) else (sflatl(s), (), 0, 0, ())


def ccanon(c):
    q, L, h, R = c
    return (q, scanon(L), h, scanon(R))


def ceqc(a, b):
    return ccanon(a) == ccanon(b)


def _unrot(P, U, R):
    for _ in range(len(P)):
        if not P or not U or P[-1] != U[-1]:
            break
        x = P[-1]
        P, U, R = P[:-1], (x,) + U[:-1], (x,) + R
    return P, U, R


def snf(s):
    pre, u, a, b, post = s
    return _unrot(tuple(pre) + tuple(u) * b, tuple(u) * a, tuple(post))


def rstrip0(l):
    l = tuple(l)
    i = len(l)
    while i and l[i - 1] == 0:
        i -= 1
    return l[:i]


def side_eqv(op, s1, s2):
    P1, U1, R1 = snf(s1)
    P2, U2, R2 = snf(s2)
    if op:
        if not U1 and not U2:
            return P1 + R1 == P2 + R2
        return P1 == P2 and U1 == U2 and R1 == R2
    if not U1 and not U2:
        return rstrip0(P1 + R1) == rstrip0(P2 + R2)
    return P1 == P2 and U1 == U2 and rstrip0(R1) == rstrip0(R2)


def cexact(a, b):
    return (a[0] == b[0] and a[2] == b[2] and side_eqv(True, a[1], b[1])
            and side_eqv(True, a[3], b[3]))


def ceqL(el, er, a, b):
    return (a[0] == b[0] and a[2] == b[2] and side_eqv(not el, a[1], b[1])
            and side_eqv(not er, a[3], b[3]))


def sapp(s1, s2):
    if sdep(s1):
        if sdep(s2):
            return None
        return (s1[0], s1[1], s1[2], s1[3], tuple(s1[4]) + sflatl(s2))
    return (sflatl(s1) + tuple(s2[0]), s2[1], s2[2], s2[3], s2[4])


def sidx(s, i0, al, be):
    pre, u, a, b, post = s
    return (pre, u, a * al, a * (i0 + be) + b, post)


def srep(w, al, be):
    return ((), tuple(w), al, be, ())


def spush(s, w):
    return (s[0], s[1], s[2], s[3], tuple(s[4]) + tuple(w))


def sshift(s):
    return (s[0], s[1], s[2], s[3] + s[2], s[4])


def cpush(c, wl, wr):
    return (c[0], spush(c[1], wl), c[2], spush(c[3], wr))


def cshift(c):
    return (c[0], sshift(c[1]), c[2], sshift(c[3]))


def link_up(I, AL, AR):
    return cexact(cpush(I[1], AL, AR), cshift(I[0]))


def link_down(I, BL, BR):
    return cexact(cshift(I[1]), cpush(I[0], BL, BR))


def at_idx(c, i0, al, be, rl, rr):
    l = sapp(sidx(c[1], i0, al, be), rl)
    r = sapp(sidx(c[3], i0, al, be), rr)
    if l is None or r is None:
        return None
    return (c[0], l, c[2], r)


def at_push(c, i0, AL, AR, al, be, rl, rr):
    tl = sapp(srep(AL, al, be), rl)
    tr = sapp(srep(AR, al, be), rr)
    if tl is None or tr is None:
        return None
    return at_idx(c, i0, 0, 0, tl, tr)


def nrun(tab, el, er, rules, segs, c):
    """Mirror of [LadderNest.nrun] (chains of BASE steps only): (conf, pos)
    or None.  [rules] is the list of (lhs, rhs) inner rules by index."""
    pos = False
    for sg in segs:
        if sg[0] == 'NCh':
            r = LC.srun(tab, el, er, sg[1], c)
            if r is None:
                return None
            c, _ca, cb = r
            pos = pos or cb != 0
            continue
        kind, k, WL, WR, i0, al, be, rl, rr, fin = sg
        if not 0 <= k < len(rules):
            return None
        I = rules[k]
        if kind == 'NUp':
            if not link_up(I, WL, WR):
                return None
            m0 = at_push(I[0], i0, WL, WR, al, be, rl, rr)
            m1 = at_idx(I[1] if fin else I[0], i0, al, be, rl, rr)
        else:
            if not link_down(I, WL, WR):
                return None
            m0 = at_idx(I[0], i0, al, be, rl, rr)
            m1 = at_push(I[1] if fin else I[0], i0, WL, WR, al, be, rl, rr)
        if m0 is None or m1 is None or not cexact(c, m0):
            return None
        c = m1
    return c, pos


def check_narm(tab, el, er, rules, lhs, rhs, segs):
    r = nrun(tab, el, er, rules, segs, lhs)
    return r is not None and r[1] and ceqL(el, er, r[0], rhs)


# ------------------------------------------------------------ concrete runs

def side_list(s, j, X):
    pre, u, a, b, post = s
    return list(pre) + list(u) * (a * j + b) + list(post) + list(X)


def conc(c, j, el, er):
    q, L, h, R = c
    return (q, side_list(L, j, [] if el else [MARK]), h,
            side_list(R, j, [] if er else [MARK]))


def _norm(lst):
    """a side list up to trailing blanks (only a side without a marker has
    an infinite blank tail)"""
    if MARK in lst:
        return tuple(lst)
    i = len(lst)
    while i and lst[i - 1] == 0:
        i -= 1
    return tuple(lst[:i])


def ckey(cfg):
    q, L, h, R = cfg
    return (q, _norm(L), h, _norm(R))


def run_lap(tab, cfg, target, cap=100000):
    """Concrete run from [cfg] to [target] (up to trailing blanks): the list
    of configurations visited, [cfg] first, target excluded; None if the run
    reads a marker, halts, or misses the target within [cap]."""
    q, L, h, R = cfg
    L, R = list(L), list(R)
    want = ckey(target)
    out = []
    for st in range(cap):
        cur = (q, tuple(L), h, tuple(R))
        if st > 0 and ckey(cur) == want:
            return out
        out.append(cur)
        if h == MARK:
            return None
        tr = tab.get((q, h))
        if tr is None:
            return None
        w, d, nq = tr
        if d > 0:
            L.insert(0, w)
            h = R.pop(0) if R else 0
        else:
            R.insert(0, w)
            h = L.pop(0) if L else 0
        q = nq
    return None


# ------------------------------------------------------- fitting inner rules

def _eqt(a, b):
    """two concrete side remainders equal up to trailing blanks"""
    return _norm(list(a)) == _norm(list(b))


def _startswith(lst, pre):
    """[lst] begins with [pre], a marker-free side reading blanks past its
    end"""
    if len(lst) >= len(pre):
        return list(lst[:len(pre)]) == list(pre)
    if MARK in lst:
        return False
    return (list(lst) == list(pre[:len(lst)])
            and all(x == 0 for x in pre[len(lst):]))


def _drop(lst, n):
    return list(lst[n:]) if len(lst) >= n else []


def _runcount(S, p, u):
    c, i = 0, p
    while S[i:i + len(u)] == u:
        c += 1
        i += len(u)
    return c


def _fit_rest_up(rests, maxq=3, maxw=6):
    """(Q, W): every consecutive pair is Q ++ W ++ T -> Q ++ T"""
    out = []
    r0 = rests[0]
    for ql in range(maxq + 1):
        for wl in range(maxw + 1):
            if ql + wl > len(r0):
                break
            Q, W = tuple(r0[:ql]), tuple(r0[ql:ql + wl])
            if MARK in Q or MARK in W:
                continue
            ok = True
            for a, b in zip(rests, rests[1:]):
                if (tuple(a[:ql]) != Q or tuple(a[ql:ql + wl]) != W
                        or not _startswith(b, Q)
                        or not _eqt(_drop(b, ql), a[ql + wl:])):
                    ok = False
                    break
            if ok:
                out.append((Q, W))
    return out


def _fit_rest_down(rests, maxq=3, maxw=6):
    """(Q, B): every consecutive pair is Q ++ T -> Q ++ B ++ T"""
    out = []
    r0, r1 = rests[0], rests[1]
    for ql in range(maxq + 1):
        for bl in range(maxw + 1):
            if ql + bl > len(r1):
                break
            Q, B = tuple(r0[:ql]), tuple(r1[ql:ql + bl])
            if len(Q) < ql or MARK in Q or MARK in B:
                continue
            ok = True
            for a, b in zip(rests, rests[1:]):
                if (not _startswith(a, Q) or not _startswith(b, Q)
                        or tuple(b[ql:ql + bl]) != B
                        or not _eqt(_drop(b, ql + bl), _drop(a, ql))):
                    ok = False
                    break
            if ok:
                out.append((Q, B))
    return out


def _flat(w):
    return (tuple(w), (), 0, 0, ())


def rule_candidates(occ, maxp=3, maxu=3):
    """Inner-rule hypotheses (kind, sigma, lhs, rhs, WL, WR) fitted to the
    consecutive visits [occ] (all at one state/symbol)."""
    q, h = occ[0][0], occ[0][2]
    seen = set()
    for sig in (1, 3):
        rho = 4 - sig
        Ss = [list(o[sig]) for o in occ]
        Os = [list(o[rho]) for o in occ]
        for p in range(maxp + 1):
            P = tuple(Ss[0][:p])
            if len(P) < p or MARK in P or any(tuple(S[:p]) != P for S in Ss):
                continue
            for ul in range(1, maxu + 1):
                u = Ss[0][p:p + ul]
                if len(u) < ul or MARK in u:
                    continue
                cs = [_runcount(S, p, u) for S in Ss]
                ds = {b - a for a, b in zip(cs, cs[1:])}
                if len(ds) != 1:
                    continue
                d = ds.pop()
                if d == 0:
                    continue
                a = abs(d)
                for t in range(3):
                    cst = [c - t for c in cs]
                    if min(cst) < 0:
                        break
                    rests = [S[p + c * ul:] for S, c in zip(Ss, cst)]
                    u_ = tuple(u)
                    if d > 0:
                        for Q, W in _fit_rest_up(rests):
                            for K, A in _fit_rest_up(Os):
                                for base in _bases(cst[0], a):
                                    Pm = P + u_ * base
                                    sL = (Pm, u_, a, 0, Q + W)
                                    sR = (Pm, u_, a, a, Q)
                                    lo, ro = _flat(K + A), _flat(K)
                                    mk = _mk(q, h, sig, sL, sR, lo, ro)
                                    WL, WR = (A, W) if sig == 3 else (W, A)
                                    key = ('NUp',) + mk + (WL, WR)
                                    if key not in seen:
                                        seen.add(key)
                                        yield ('NUp', sig, mk[0], mk[1], WL, WR)
                    else:
                        for Q, B in _fit_rest_down(rests):
                            for K, Bo in _fit_rest_down(Os):
                                for base in _bases(cst[-1] - a, a):
                                    Pm = P + u_ * base
                                    sL = (Pm, u_, a, a, Q)
                                    sR = (Pm, u_, a, 0, Q + B)
                                    lo, ro = _flat(K), _flat(K + Bo)
                                    mk = _mk(q, h, sig, sL, sR, lo, ro)
                                    WL, WR = (Bo, B) if sig == 3 else (B, Bo)
                                    key = ('NDn',) + mk + (WL, WR)
                                    if key not in seen:
                                        seen.add(key)
                                        yield ('NDn', sig, mk[0], mk[1], WL, WR)


def _bases(c, a, most=4):
    """the constant part of a run of [c] copies stepping by [a], smallest
    first: every copy of it is materialised in [s_pre], because the chain
    engine can fold copies into a count but never unfold one"""
    if c < 0:
        c = 0
    return [c % a + k * a for k in range(most)]


def _mk(q, h, sig, sL, sR, lo, ro):
    if sig == 3:
        return (q, lo, h, sL), (q, ro, h, sR)
    return (q, sL, h, lo), (q, sR, h, ro)


# ---------------------------------------------- matching a visit to a rule

def match_at(cfg, side_conf, i):
    """tails (TL, TR) if the concrete [cfg] is [side_conf] at index [i]
    followed by some tails, else None"""
    q, L, h, R = cfg
    if q != side_conf[0] or h != side_conf[2]:
        return None
    pl = side_list(side_conf[1], i, [])
    pr = side_list(side_conf[3], i, [])
    if not _startswith(L, pl) or not _startswith(R, pr):
        return None
    return _drop(L, len(pl)), _drop(R, len(pr))


def rounds(occ, I, kind, imax=64):
    """The first maximal run of consecutive visits the rule [I] steps
    through: (s, i0, n, fin), where visit [s] is the rule's lhs at its first
    index, [n] rounds follow on the lhs, and [fin] says one more visit is the
    rhs."""
    lhs, rhs = I
    for s in range(len(occ)):
        for i in range(imax):
            if match_at(occ[s], lhs, i) is None:
                continue
            step = 1 if kind == 'NUp' else -1
            n = 0
            while (s + n + 1 < len(occ) and 0 <= i + step * (n + 1)
                   and match_at(occ[s + n + 1], lhs, i + step * (n + 1))
                   is not None):
                n += 1
            if n == 0:
                continue
            ie = i + step * n
            fin = (s + n + 1 < len(occ)
                   and match_at(occ[s + n + 1], rhs, ie) is not None)
            i0 = i if kind == 'NUp' else ie
            return s, i0, n, fin
    return None


# ---------------------------------------------------------------- the search

def _occs(tr, key):
    return [c for c in tr if (c[0], c[2]) == key]


def _affine(xs, js):
    """(al, be) with x = al*j + be over every sample, al, be >= 0"""
    if len(set(xs)) == 1 and len(xs) >= 2:
        return 0, xs[0]
    d = (xs[1] - xs[0]) // (js[1] - js[0]) if js[1] != js[0] else None
    if d is None or d <= 0:
        return None
    be = xs[0] - d * js[0]
    if be < 0 or any(x != d * j + be for x, j in zip(xs, js)):
        return None
    return d, be


def _rest_list(tail, W, n):
    """the tail after [n] copies of [W], or None"""
    w = list(W) * n
    if not _startswith(tail, w):
        return None
    return _drop(tail, len(w))


def _rest_side(lst):
    """a concrete remainder as a flat side, the marker (the arm's own tail)
    stripped"""
    lst = list(lst)
    if MARK in lst:
        lst = lst[:lst.index(MARK)]
    else:
        lst = list(_norm(lst))
    return _flat(lst)


def _reparse(c1, I, kind, fin, i0, al, be, WL, WR, landed):
    """rests (rl, rr) such that the segment's m0 IS [landed], syntactically
    after canonical forms; None if no such rests"""
    lhs = I[0]
    rs = []
    for k, W in ((1, WL), (3, WR)):
        tgt = scanon(landed[k])
        if kind == 'NUp':
            head = sidx(lhs[k], i0, 0, 0)
            if W and al:
                # K A^(al j + be) rest: [tgt] must be (K, A, al, be, rest)
                if not sdep(tgt):
                    return None
                if (tuple(tgt[0]) != sflatl(head) or tuple(tgt[1]) != tuple(W)
                        or tgt[2] != al or tgt[3] != be):
                    return None
                rs.append(_flat(tgt[4]))
                continue
            pre = sflatl(head) + tuple(W) * be
        else:
            head = sidx(lhs[k], i0, al, be)
            if sdep(head):
                if not sdep(tgt) or tuple(tgt[:4]) != tuple(head[:4]):
                    return None
                post = tuple(tgt[4])
                hp = tuple(head[4])
                if post[:len(hp)] != hp:
                    return None
                rs.append(_flat(post[len(hp):]))
                continue
            pre = sflatl(head)
        # the head is concrete: strip it off the landed side
        if sdep(tgt):
            if tuple(tgt[0][:len(pre)]) != pre:
                return None
            rs.append((tuple(tgt[0][len(pre):]),) + tuple(tgt[1:]))
        else:
            fl = sflatl(tgt)
            if fl[:len(pre)] != pre:
                return None
            rs.append(_flat(fl[len(pre):]))
    return rs[0], rs[1]


def derive_nested(tab, el, er, c0, c1, depth=2, js=(4, 5, 6, 7), budget=None,
                  maxdepth=32, nmax=120):
    """(segs, inner_rules) proving [c0] ->+ [c1] (at flags el/er) by a
    segment program, or None.  inner_rules is [(lhs, rhs, chain)]; a
    segment's [k] is relative to that list."""
    laps = {}
    for j in js:
        tr = run_lap(tab, conc(c0, j, el, er), conc(c1, j, el, er))
        if tr is None:
            return None
        laps[j] = tr
    return _search(tab, el, er, c0, c1, laps, list(js), depth, maxdepth, nmax)


def _search(tab, el, er, c0, c1, laps, js, depth, maxdepth, nmax):
    jb = js[-1]
    keys = {}
    for c in laps[jb]:
        keys[(c[0], c[2])] = keys.get((c[0], c[2]), 0) + 1
    cands = []
    for key in keys:
        cnt = [len(_occs(laps[j], key)) for j in js]
        aff = _affine(cnt, js)
        if aff is None or aff[0] == 0:
            continue
        cands.append((aff[0], cnt[-1], key))
    cands.sort()
    tried = set()
    for _al, _n, key in cands:
        occ = _occs(laps[jb], key)
        if len(occ) < 4:
            continue
        mid_ = occ[1:-1]
        for win in (mid_, occ):
            if len(win) < 3:
                continue
            for kind, sig, lhs, rhs, WL, WR in rule_candidates(win):
                if (lhs, rhs, WL, WR) in tried:
                    continue
                tried.add((lhs, rhs, WL, WR))
                got = _try_rule(tab, el, er, c0, c1, laps, js, kind, lhs, rhs,
                                WL, WR, key, depth, maxdepth, nmax)
                if got is not None:
                    return got
    return None


def _try_rule(tab, el, er, c0, c1, laps, js, kind, lhs, rhs, WL, WR, key,
              depth, maxdepth, nmax):
    I = (lhs, rhs)
    ok = link_up(I, WL, WR) if kind == 'NUp' else link_down(I, WL, WR)
    if not ok:
        return None
    # the round count across j
    per = []
    for j in js:
        r = rounds(_occs(laps[j], key), I, kind)
        if r is None:
            return None
        per.append(r)
    if len({r[1] for r in per}) != 1:
        return None
    i0 = per[0][1]
    ns = [r[2] - (0 if kind == 'NUp' else 0) for r in per]
    aff = _affine(ns, js)
    if aff is None:
        return None
    al, be = aff
    # the inner rule, proved with both tails opaque
    ich = LC.derive_chain(tab, False, False, lhs, rhs, maxdepth=maxdepth,
                          nmax=nmax, lift=True)
    if ich is None:
        return None
    got = LC.srun(tab, False, False, ich, lhs)
    if got is None or not cexact(got[0], rhs):
        return None
    # the rule is stated to what the chain REACHES; the link compares normal
    # forms, so a different spelling of the same side is fine
    rhs = got[0]
    I = (lhs, rhs)
    ok = link_up(I, WL, WR) if kind == 'NUp' else link_down(I, WL, WR)
    if not ok:
        return None
    # the rests, read off the first visit at the largest j
    j = js[-1]
    s, _i0, n, fin = per[-1]
    first = _occs(laps[j], key)[s]
    if kind == 'NUp':
        t = match_at(first, lhs, i0)
        if t is None:
            return None
        rl = _rest_list(t[0], WL, al * j + be)
        rr = _rest_list(t[1], WR, al * j + be)
    else:
        t = match_at(first, lhs, i0 + al * j + be)
        if t is None:
            return None
        rl, rr = t
    if rl is None or rr is None:
        return None
    rl, rr = _rest_side(rl), _rest_side(rr)
    for fin_ in ([True, False] if fin else [False, True]):
        if kind == 'NUp':
            m0 = at_push(lhs, i0, WL, WR, al, be, rl, rr)
        else:
            m0 = at_idx(lhs, i0, al, be, rl, rr)
        if m0 is None:
            return None
        # the chain into the first round
        if cexact(c0, m0):
            pre, landed = [], c0
        else:
            pre = LC.derive_chain(tab, el, er, c0, m0, maxdepth=maxdepth,
                                  nmax=nmax, lift=True)
            if pre is None:
                return None
            got = LC.srun(tab, el, er, pre, c0)
            if got is None:
                return None
            landed = got[0]
        rr2 = _reparse(c1, I, kind, fin_, i0, al, be, WL, WR, landed)
        if rr2 is None:
            return None
        rl2, rrr2 = rr2
        seg = (kind, 0, tuple(WL), tuple(WR), i0, al, be, rl2, rrr2, fin_)
        body = [('NCh', pre)] if pre else []
        body.append(seg)
        mid = nrun(tab, el, er, [I], body, c0)
        if mid is None:
            continue
        m1 = mid[0]
        # the chain out of the last round
        post = LC.derive_chain(tab, el, er, m1, c1, maxdepth=maxdepth,
                               nmax=nmax, lift=True)
        segs = None
        rules = [(lhs, rhs, ich)]
        if post is not None:
            got = LC.srun(tab, el, er, post, m1)
            if got is not None and ceqL(el, er, got[0], c1):
                segs = body + [('NCh', post)]
        if segs is None and depth > 1:
            sub = derive_nested(tab, el, er, m1, c1, depth=depth - 1,
                                js=tuple(js), maxdepth=maxdepth, nmax=nmax)
            if sub is not None:
                ssegs, srules = sub
                segs = body + [_shift(sg, 1) for sg in ssegs]
                rules = rules + srules
        if segs is None:
            continue
        if check_narm(tab, el, er, [(r[0], r[1]) for r in rules], c0, c1, segs):
            return segs, rules
    return None


def _shift(sg, k):
    if sg[0] == 'NCh':
        return sg
    return (sg[0], sg[1] + k) + tuple(sg[2:])
