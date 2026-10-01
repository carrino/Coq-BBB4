#!/usr/bin/env python3
"""BLC4: blc3/lg3.py's joint-language list glue with END WORDS on both sides
and any unit (UNTRUSTED finder; SCOPING_INSTR.md §7.4.BLC4).

lg3 assumed a list of `1`-blocks whose b_0 borders the blank tape and whose
far end is a pinned last block followed by blank.  The `0`-block lists
(`1111 0^994 11011 0^497 111111 ...`) have a constant word BEYOND b_0 and a
constant word after the last block, so here:

  * the LEFT tail may end in a TERMINATOR item: kind (left end word, unit),
    exponent 0, relation `up, a = 0, d = 0` (e = 0, the pred b_0 free), into
    the accepting state 'LT' (state 'L0', the one after b_0, is then not
    accepting);
  * the RIGHT tail's END item is (end word, unit) with exponent 0 pinning
    b_k (`down, a = 0, d = b_k`), one kind per end word; the END word () is
    lg3's `0` cell.

Both are plain ListGlueTr items, so ListGlue2Tr checks them unchanged.
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
import lg3                                        # noqa: E402
import lg_batch as G                              # noqa: E402
import ti_batch as T                              # noqa: E402
import ti_coq as C                                # noqa: E402

Fail, NonCanon = T.Fail, G.NonCanon
aeq, acoefs = G.aeq, G.acoefs
KEEP = lg3.KEEP
VERBOSE = lg3.VERBOSE
DSLACK = int(os.environ.get('LG4_DSLACK', '4'))


class Lang4(lg3.Lang):
    """lg3.Lang with a unit and separators PER SIDE and end words.

    fwd, q0: F over the RIGHT form's symbols (w, d) (the anchor's list);
    end[q] = [(x, bk, endw)];
    lstart / lfwd: the LEFT tails' automaton over the left form's symbols
      (wL, dL), on F's states (the passed elements' F-states, learned by
      aligning each left sample to the list it was swept from);
    lends: the words beyond b_0 in a LEFT tail (tape order, read outward),
      empty when b_0 borders the blank tape."""

    def __init__(self, a, unit, fwd, end, q0, lfwd, lstart, seps, lends=(), unitL=None,
                 sepsL=None, psepsR=(), psepsL=()):
        self.a, self.unit = a, tuple(unit)
        self.unitL = tuple(unit if unitL is None else unitL)
        self.fwd, self.q0, self.shift = dict(fwd), q0, 0
        self.end4 = {q: list(lst) for q, lst in end.items()}
        self.end = {q: [(x, bk) for x, bk, _ in lst] for q, lst in end.items()}
        self.lfwd, self.lstart = dict(lfwd), list(lstart)
        ws = set(x[0] for (_, x) in self.fwd) | set(x[0] for lst in self.end.values()
                                                   for x, _ in lst)
        self.seps = sorted(set(seps or ()) | ws, key=lambda w: (-len(w), w))
        wl = set(x[0] for (_, x) in self.lfwd) | set(x[0] for x, _ in self.lstart)
        self.sepsL = sorted(set(sepsL or ()) | wl, key=lambda w: (-len(w), w))
        self.lends = sorted(set(tuple(w) for w in lends), key=lambda w: (-len(w), w))
        # one-cell units: the cell words lg3.parse merges into separators
        self.psepsR = sorted(set(tuple(w) for w in psepsR) | set(w[1] for w in self.seps),
                             key=lambda w: (-len(w), w))
        self.psepsL = sorted(set(tuple(w) for w in psepsL) | set(w[1] for w in self.sepsL),
                             key=lambda w: (-len(w), w))
        self.endws = sorted(set(w for lst in self.end4.values() for _, _, w in lst),
                            key=lambda w: (-len(w), w))
        ds = [abs(x[1]) for (_, x) in self.fwd] + [abs(x[1]) for (_, x) in self.lfwd] + \
            [abs(x[1]) for x, _ in self.lstart] + [0]
        self.dmax = max(ds) + DSLACK

    def automaton(self):
        nfa = G.NFA()
        u, uL = self.unit, self.unitL
        # a separator symbol is (unit before, gap cells, unit after) in tape
        # order: a RIGHT item is the gap and the element after it, a LEFT
        # item (nearest-first) the gap and the element before it
        kL = {w: nfa.kind('L', tuple(reversed(w[1])), tuple(reversed(w[0]))) for w in self.sepsL}
        kR = {w: nfa.kind('R', tuple(w[1]), tuple(w[2])) for w in self.seps}
        kE = {w: nfa.kind('R', tuple(w) if w else (0,), u) for w in self.endws}
        kT = {w: nfa.kind('L', tuple(reversed(w)), tuple(reversed(uL))) for w in self.lends}
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
        byq = collections.defaultdict(list)
        for (q, x), q2 in self.lfwd.items():
            byq[q].append((x, q2))
        seen, todo = set(), []
        for (w, d), q2 in self.lstart:
            add('L', ('F', q2), kL[w], 'L0', (True, a, d))
            todo.append(q2)
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.add(q)
            for (w, d), q2 in byq[q]:
                add('L', ('F', q2), kL[w], ('F', q), (True, a, d))
                todo.append(q2)
        if self.lends:
            for w in self.lends:
                add('L', 'L0', kT[w], 'LT', (True, 0, 0))
            nfa.acc.add(('L', 'LT'))
        else:
            nfa.acc.add(('L', 'L0'))
        start = frozenset([('FIN',)])
        rstates = {}
        todo = []
        byend = collections.defaultdict(set)
        ends = []
        for q, lst in self.end4.items():
            for x, bk, w in lst:
                ends.append((q, x, bk, w))
                byend[(bk, w)].add(('Z', q, x, bk, w))
        for (bk, w), zs in byend.items():
            s = frozenset(zs)
            add('R', ('R', s), kE[w], ('R', start), (False, 0, bk))
            todo.append(s)
        pred = collections.defaultdict(set)
        for (q, x), q2 in self.fwd.items():
            pred[(q2, x)].add(q)
        syms = sorted(set(x for (_, x) in self.fwd) | set(e[1] for e in ends))
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
        self.nfa, self.foldmap, self.kL, self.kR, self.kE, self.kT = nfa, fold, kL, kR, kE, kT
        self.rstart = ('R', start)
        return nfa


def tok_cells(toks):
    """the cells of tokens (constant blocks expanded), or None"""
    out = []
    for t in toks:
        if t[0] == 'c':
            out.append(t[1])
        elif acoefs(t[2]):
            return None
        else:
            out.extend(C.rep(t[1], t[2][0]))
    return tuple(out)


class NeedMod(Exception):
    """a leaf lands where a split element's residue is not fixed: refine the
    region of variable k mod m"""

    def __init__(self, k, m):
        self.k, self.m = k, m


Req = T.Req
nfa_maxs = lg3.nfa_maxs
SPLITGAP = int(os.environ.get('LG4_SPLITGAP', '3'))
SPLITMOD = os.environ.get('LG4_SPLITMOD', '1') == '1'


class X4(lg3.X3):
    """lg3.X3 with per-side units, end words (Lang4) and split elements
    (explore_fam is lg3's, plus the NeedMod refinement)"""

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


    def fam_of(self, q, h, L, R, tails, boot=False):
        lang = self.lang
        toks = lg3.tape_tokens(L, h, R)
        hidx = next(i for i, t in enumerate(toks) if t[-1] == 'H')
        elL = parse4(toks, lang.unitL, lang.psepsL, 'L')
        elR = parse4(toks, lang.unit, lang.psepsR, 'R')

        def mkdist(el):
            Es = [k for k, x in enumerate(el) if x[0] == 'E']

            def dist(k):
                x = el[k]
                if x[1] <= hidx < x[2]:
                    return 0
                if x[2] <= hidx:
                    return sum(1 for k2 in Es if k2 >= k and el[k2][2] <= hidx)
                return sum(1 for k2 in Es if k2 <= k and el[k2][1] > hidx)
            return dist
        folds = {'L': [], 'R': []}
        specs = {}
        for sd, el in (('L', elL), ('R', elR)):
            tl = tails[sd]
            if tl is None:
                continue
            k = 0 if sd == 'L' else len(el) - 1
            if not el or el[k][0] != 'E' or not aeq(el[k][3], tl[1]):
                raise NonCanon(sd)
        a = lang.a
        # LEFT
        el, dist = elL, mkdist(elL)
        sepw = set(lang.sepsL)

        def word(g):
            w = word_at(el, toks, g, lang.unitL, lang.psepsL)
            return w if w in sepw else None
        cur = tails['L'][0] if tails['L'] is not None else None
        fl = []
        k = 0
        if cur is None and el:
            if lang.lends:
                for j in range(1, len(el)):
                    if el[j][0] != 'E' or el[j - 1][0] != 'G':
                        continue
                    if not (dist(j) > KEEP and
                            all(toks[i][-1] == 'L' for i in range(0, el[j][2]))):
                        break
                    w = tok_cells(toks[0:el[j][1]])
                    if w in lang.kT:
                        ti = self.foldmap.get(('L', 'LT', lang.kT[w], (True, 0, 0)))
                        if ti is not None:
                            fl.insert(0, (ti, (0, ())))
                            cur = self.nfa.trans[ti][1]
                            k = j
                            break
            elif el[0][0] != 'G':
                cur = 'L0'
        while cur is not None and k + 2 < len(el) and el[k][0] == 'E' and \
                el[k + 1][0] == 'G' and word(k + 1) is not None and \
                el[k + 2][0] == 'E' and dist(k) > KEEP and \
                all(toks[i][-1] == 'L' for i in range(el[k][1], el[k + 1][2])):
            d = lg3.rel_of(True, a, el[k + 2][3], el[k][3])
            if d is None:
                break
            w = word(k + 1)
            ti = self.foldmap.get(('L', cur, lang.kL[w], (True, a, d)))
            if ti is None:
                break
            fl.insert(0, (ti, el[k][3]))
            cur = self.nfa.trans[ti][1]
            k += 2
        lo = k
        if cur is not None and (fl or tails['L'] is not None):
            if lo >= len(el) or el[lo][0] != 'E':
                raise Fail('left tail without a ref')
            specs['L'] = (cur, el[lo][3])
            folds['L'] = fl
            starttok = el[lo][1]
        else:
            specs['L'] = None
            starttok = 0
        # RIGHT
        el, dist = elR, mkdist(elR)
        sepw = set(lang.seps)

        def word(g):
            w = word_at(el, toks, g, lang.unit, lang.psepsR)
            return w if w in sepw else None
        lo = 0
        while lo < len(el) and el[lo][2] <= starttok:
            lo += 1
        cur = tails['R'][0] if tails['R'] is not None else None
        fr = []
        k = len(el) - 1
        if cur is None and el:
            for w in lang.endws:
                if w:
                    # the window ends with the cells of w, after a constant element
                    kk = None
                    for j in range(len(el) - 1, lo, -1):
                        if el[j][0] == 'G' and el[j - 1][0] == 'E':
                            cs = tok_cells(toks[el[j][1]:el[-1][2]])
                            if cs == w:
                                kk = j - 1
                                break
                    if kk is None:
                        continue
                else:
                    kk = len(el) - 1
                if el[kk][0] != 'E' or acoefs(el[kk][3]) or dist(kk) <= KEEP or \
                        not all(toks[i][-1] == 'R' for i in range(el[kk][1], el[-1][2])):
                    continue
                ti = self.foldmap.get(('R', lang.rstart, lang.kE[w], (False, 0, el[kk][3][0])))
                if ti is None:
                    continue
                fr.insert(0, (ti, (0, ())))
                cur = self.nfa.trans[ti][1]
                k = kk
                break
        while cur is not None and k - 2 >= lo and el[k][0] == 'E' and \
                el[k - 1][0] == 'G' and word(k - 1) is not None and \
                el[k - 2][0] == 'E' and dist(k) > KEEP and \
                all(toks[i][-1] == 'R' for i in range(el[k - 1][1], el[k][2])):
            d = lg3.rel_of(False, a, el[k - 2][3], el[k][3])
            if d is None:
                break
            w = word(k - 1)
            ti = self.foldmap.get(('R', cur, lang.kR[w], (False, a, d)))
            if ti is None:
                break
            fr.insert(0, (ti, el[k][3]))
            cur = self.nfa.trans[ti][1]
            k -= 2
        if cur is not None and (fr or tails['R'] is not None):
            hi = k + 1
            if hi - 1 < lo or el[hi - 1][0] != 'E':
                raise Fail('right tail without a ref')
            specs['R'] = (cur, el[hi - 1][3])
            folds['R'] = fr
            endtok = el[hi - 1][2]
        else:
            specs['R'] = None
            hi = len(el)
            endtok = el[-1][2] if el else 0
        if starttok >= endtok:
            raise Fail('empty window')
        wt = []
        for i in range(starttok, endtok):
            wt.append((i, toks[i]))
        return self._finish(q, h, toks, hidx, wt, specs, folds)

    def _finish(self, q, h, toks, hidx, wt, specs, folds):
        a = self.lang.a
        Lw, Rw = [], []
        for i, t in wt:
            if t[-1] == 'H':
                continue
            dst = Lw if i < hidx else Rw
            if t[0] == 'c':
                dst.append(('L', (t[1],)))
            else:
                e = t[2]
                if not acoefs(e) and len(t[1]) * e[0] <= lg3.SMALL:
                    dst.append(('L', C.rep(t[1], e[0])))
                else:
                    dst.append(('B', tuple(t[1]), e))
        Lw = G.fnorm(list(reversed([(x[0], tuple(reversed(x[1]))) if x[0] == 'L' else
                                    ('B', tuple(reversed(x[1])), x[2]) for x in Lw])))
        Rw = G.fnorm(Rw)
        Lw = self._blockify(Lw)
        Rw = self._blockify(Rw)
        if specs['L'] is None:
            Lw = C.nstrip(Lw)
        if specs['R'] is None:
            Rw = C.nstrip(Rw)
        exps = T.exps(Lw) + T.exps(Rw)
        for sd in ('L', 'R'):
            if specs[sd] is not None:
                exps.append(specs[sd][1])
        wbl = [x[2] for x in reversed(Lw) if x[0] == 'B'] + [x[2] for x in Rw if x[0] == 'B']
        wrel = []
        dmax = self.lang.dmax
        for x, y in zip(wbl, wbl[1:]):
            d = lg3.rel_of(False, a, x, y)
            # a digit far outside the language's is no list relation (the
            # two halves of an element the sweep is rewriting, say)
            wrel.append(d if d is not None and abs(d) <= dmax else None)
        for sd, blk in (('L', wbl[:1]), ('R', wbl[-1:])):
            if specs[sd] is not None and blk:
                wrel.append(lg3.rel_of(True, 1, blk[0], specs[sd][1]))
        key = (q, h, T.shape(Lw), T.shape(Rw),
               None if specs['L'] is None else specs['L'][0],
               None if specs['R'] is None else specs['R'][0], tuple(wrel))
        if SPLITMOD:
            res = self._split_res(Lw, Rw)
            if res:
                key = key[:6] + (key[6] + (('res',) + res,),)
        if key not in self.fidx:
            if len(self.fams) >= G.MAXFAM:
                raise Fail('too many families')
            self.fidx[key] = len(self.fams)
            self.fams.append(lg3.LFam(key))
            if VERBOSE:
                print('  new family %d: %s' % (len(self.fams) - 1, lg3.fmt_key(key)),
                      file=sys.stderr)
        fid = self.fidx[key]
        F = self.fams[fid]
        ch = False
        if F.match(exps) is None:
            ch = F.join(exps)
            if F.match(exps) is None:
                raise Fail('join does not cover its target')
        return fid, exps, ch, folds


def explore_row(spec, lang, t0, mir=False):
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        raise Fail('halts')
    pins = set(k for k in tab if k not in r2[4])
    CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
    X = X4(tab, pins, lang)
    boot = lg3.boot_of(X, tab, t0)
    X.explore(boot)
    return X, pins, boot


def find_dir(spec, lang, t0, mir=False, plist=G.PLIST):
    X, pins, boot = explore_row(spec, lang, t0, mir)
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
        lv = G.l_live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = G.c_check(cert, tab) or (None if lg3.c_maxs_ok(cert) else 'maxs')
            if err:
                return dict(err='check: ' + err)
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


def _split_res(self, Lw, Rw):
    """the residues mod the ratio of the two halves of every SPLIT element
    (two window blocks of different units with at most SPLITGAP cells, the
    head's included, between them): the family is then a lattice on which
    the neighbour relation of the element's SUM has a nonnegative
    parametrisation.  Raises NeedMod when a half's residue is not fixed"""
    a = self.lang.a
    tape = []
    for x in reversed(Lw):
        tape.append(('B', tuple(reversed(x[1])), x[2]) if x[0] == 'B' else ('L', len(x[1])))
    tape.append(('L', 1))
    for x in Rw:
        tape.append(('B', tuple(x[1]), x[2]) if x[0] == 'B' else ('L', len(x[1])))
    blks = []
    gap = 0
    last = None
    for x in tape:
        if x[0] == 'L':
            gap += x[1]
            continue
        cur = len(blks)
        blks.append([x[1], x[2], False])
        if last is not None and gap <= SPLITGAP and C.primroot(blks[last][0])[0] != \
                C.primroot(x[1])[0]:
            blks[last][2] = True
            blks[cur][2] = True
        last = cur
        gap = 0
    res = []
    for u, e, mark in blks:
        if not mark:
            continue
        for k, m in acoefs(e):
            if m % a:
                raise NeedMod(k, a)
        res.append(e[0] % a)
    return tuple(res)


def _blockify_units(self, side):
    """lg3.X3._blockify for every unit of the language (both sides'):
    a literal run of a one-cell unit longer than SMALL is a constant block"""
    us = []
    for u in (self.lang.unit, getattr(self.lang, 'unitL', self.lang.unit),
              tuple(reversed(self.lang.unit)), tuple(reversed(getattr(self.lang, 'unitL', self.lang.unit)))):
        if u not in us:
            us.append(u)
    out = []
    for x in side:
        if x[0] != 'L':
            out.append(x)
            continue
        w = tuple(x[1])
        i = 0
        lit = []
        if any(len(u) > 1 for u in us):
            # multi-cell units: the far-aligned stretches (see parse4)
            spans = []
            for u in us:
                if len(u) == 1:
                    continue
                for s0, e0, uu in stretch_elems(list(w), len(u), rotations(u), 'R'):
                    if e0 - s0 > lg3.SMALL:
                        spans.append((s0, e0, uu))
            spans.sort()
            pos = 0
            for s0, e0, uu in spans:
                if s0 < pos:
                    continue
                if s0 > pos:
                    out.extend(self._blockify1(w[pos:s0], us))
                out.append(('B', uu, ((e0 - s0) // len(uu), ())))
                pos = e0
            if pos < len(w):
                out.extend(self._blockify1(w[pos:], us))
            continue
        while i < len(w):
            best = None
            for u in us:
                if len(u) > 1:
                    continue
                n = 0
                while w[i + n * len(u):i + (n + 1) * len(u)] == u:
                    n += 1
                if n * len(u) > lg3.SMALL and (best is None or n * len(u) > best[1] * len(best[0])):
                    best = (u, n)
            if best is not None:
                if lit:
                    out.append(('L', tuple(lit)))
                    lit = []
                out.append(('B', best[0], (best[1], ())))
                i += best[1] * len(best[0])
            else:
                lit.append(w[i])
                i += 1
        if lit:
            out.append(('L', tuple(lit)))
    return out


def _blockify1(self, w, us):
    """the one-cell units' blocks of a literal word"""
    us1 = [u for u in us if len(u) == 1]
    out, lit, i = [], [], 0
    w = tuple(w)
    while i < len(w):
        best = None
        for u in us1:
            n = 0
            while w[i + n:i + n + 1] == u:
                n += 1
            if n > lg3.SMALL and (best is None or n > best[1]):
                best = (u, n)
        if best is not None:
            if lit:
                out.append(('L', tuple(lit)))
                lit = []
            out.append(('B', best[0], (best[1], ())))
            i += best[1]
        else:
            lit.append(w[i])
            i += 1
    if lit:
        out.append(('L', tuple(lit)))
    return out


X4._blockify = _blockify_units
X4._blockify1 = _blockify1
X4._split_res = _split_res


# ------------------------------------------------- multi-cell units ----
#
# A list of a multi-cell unit (`(110)^611 000 (011)^153 ...`) can be written
# as blocks in several rotations (`11 (011)^e` is `(110)^e 11`), and the
# checker compares segments syntactically.  So the finder fixes ONE form:
# in a side's nearest-first order, every block of a multi-cell unit is
# pushed as far from the head as it goes (no more `SRot 1` applies).  That
# depends only on cells beyond the block, which a leaf that does not cross
# it never touches; a leaf that crosses a block ends with the `SRot 1`
# steps that restore it (leaf_run4).  On a concrete tape the same form is
# the periodic STRETCH aligned to its far end: whole units ending where the
# periodicity breaks, the partial unit at the near end in the gap.

MINCOPY = int(os.environ.get('LG4_MINCOPY', '2'))


def rotations(W):
    W = tuple(W)
    return set(W[i:] + W[:i] for i in range(len(W)))


def stretch_elems(cells, p, rots, align, mincopy=MINCOPY):
    """(s, e, unit) of the elements in a cell word: maximal periodic
    stretches of period p whose unit is in rots, as whole units aligned to
    the END of the word (align 'R') or to its start ('L'); overlapping
    neighbours are clipped"""
    n = len(cells)
    st = []
    j = p
    while j < n:
        if cells[j] != cells[j - p]:
            j += 1
            continue
        a = j
        while j < n and cells[j] == cells[j - p]:
            j += 1
        st.append((a - p, j))
    out = []
    if align == 'R':
        prev = 0
        for s, e in st:
            s = max(s, prev)
            k = (e - s) // p
            if k < mincopy:
                continue
            u = tuple(cells[e - p * k:e - p * k + p])
            if u not in rots:
                continue
            out.append((e - p * k, e, u))
            prev = e
    else:
        nxt = n
        for s, e in reversed(st):
            e = min(e, nxt)
            k = (e - s) // p
            if k < mincopy:
                continue
            u = tuple(cells[s:s + p])
            if u not in rots:
                continue
            out.insert(0, (s, s + p * k, u))
            nxt = s
    return out


def parse4(toks, W, pseps, align):
    """the tokens as elements ('E', i0, i1, exp, unit) and gaps ('G', i0,
    i1, toks) in tape order.  A one-cell unit is lg3.parse's (separator
    words pseps merged); a multi-cell unit: a block of a rotation of W, or
    a periodic stretch in a run of literal cells"""
    W = tuple(W)
    if len(W) == 1:
        el = lg3.parse(toks, W, pseps)
        return [x + (W,) if x[0] == 'E' else x for x in el]
    p = len(W)
    rots = rotations(W)
    es = []
    i, n = 0, len(toks)
    while i < n:
        t = toks[i]
        if t[0] == 'b':
            if tuple(t[1]) in rots:
                es.append((i, i + 1, t[2], tuple(t[1])))
            i += 1
            continue
        j = i
        while j < n and toks[j][0] == 'c':
            j += 1
        cells = [toks[k][1] for k in range(i, j)]
        for s, e, u in stretch_elems(cells, p, rots, align):
            es.append((i + s, i + e, ((e - s) // p, ()), u))
        i = j
    out = []
    pos = 0
    for i0, i1, e, u in es:
        if i0 > pos or (out and out[-1][0] == 'E'):
            # (an empty gap between two elements of different rotations)
            out.append(('G', pos, i0, tuple(toks[pos:i0])))
        out.append(('E', i0, i1, e, u))
        pos = i1
    if pos < n:
        out.append(('G', pos, n, tuple(toks[pos:n])))
    return out


def word_at(el, toks, g, W, pseps):
    """the separator symbol (u_before, gap cells, u_after) of gap el[g]
    between two elements, or None"""
    if g <= 0 or g + 1 >= len(el) or el[g][0] != 'G' or el[g - 1][0] != 'E' or \
            el[g + 1][0] != 'E':
        return None
    if len(W) == 1:
        c = lg3.gap_word(el[g], pseps)
    else:
        c = tok_cells(toks[el[g][1]:el[g][2]])
    if c is None:
        return None
    return (el[g - 1][4], c, el[g + 1][4])


# leaves end canonical: a crossed block of a multi-cell unit is rotated away
# from the head as far as its post allows
CANON = {'on': False}
_leaf_prev = G.leaf_run


def leaf_run4(tabw, q, h, Lz, Rz, endL, endR, na, p):
    lf = _leaf_prev(tabw, q, h, Lz, Rz, endL, endR, na, p)
    if not CANON['on']:
        return lf
    q1, L1, h1, R1 = lf['c1']
    extra = []
    sides = {'L': L1, 'R': R1}
    for sd in ('L', 'R'):
        S = sides[sd]
        if len(S[1]) <= 1:
            continue
        while True:
            s2 = C.LC.srot(1, S)
            if s2 is None:
                break
            S = s2
            extra.append(('SRot' + sd, 1))
        sides[sd] = S
    if not extra:
        return lf
    chain = list(lf['chain']) + extra
    r = C.LC.srun(tabw, lf['el'], lf['er'], chain, lf['c0'])
    if r is None:
        raise Fail('canonical rotation does not replay')
    c1 = r[0]
    j = lf['j']
    lf = dict(lf)
    lf.update(chain=chain, c1=c1, q1=c1[0], h1=c1[2],
              endL=C.ss_segs(c1[1], j) + Lz[lf['nL']:],
              endR=C.ss_segs(c1[3], j) + Rz[lf['nR']:])
    return lf


G.leaf_run = leaf_run4
