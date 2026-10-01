"""MP: blc4/lg4.Lang4 whose RIGHT tail states also count the items read from
the far end, capped at DEPTH (UNTRUSTED; SCOPING_INSTR.md §7.4.MP).

Lang4's right automaton is the determinised reverse of F: a state is the set
of F-states from which the rest of the list is accepted.  Nothing in it says
how LONG the rest is, so an unfold far from the far end still has a kid
"the next item is the END" and the exploration simulates two-element lists
with tiny blocks, which the machine never builds and whose runs leave the
language (on the ratio-4 lists: hundreds of such families).  With the count
c = min(DEPTH, items to the far end) in the state, an END kid exists only at
c = 1, and ListGlueTr's per-state lower bound (lc_mins: the END pins b_k, and
each relation multiplies by the ratio) makes every constant region below
a^c b_k void.  The automaton stays a plain ListGlueTr automaton; nothing in
the checker changes.
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc4'))
import lg4                                          # noqa: E402
import lg_batch as G                                # noqa: E402
import ti_batch as T                                # noqa: E402

DEPTH = int(os.environ.get('MP_DEPTH', '3'))
ROT = os.environ.get('MP_ROT', '1') == '1'
Fail = T.Fail


class Lang4D(lg4.Lang4):
    depth = DEPTH

    def automaton(self):
        nfa = G.NFA()
        u, uL = self.unit, self.unitL
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
        # LEFT: as Lang4
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
        if self.lend_blank:
            nfa.acc.add(('L', 'L0'))
        # RIGHT: (determinised reverse state, items to the far end capped)
        D = self.depth
        start = (frozenset([('FIN',)]), 0)
        rstates = {}
        todo = []
        byend = collections.defaultdict(set)
        ends = []
        for q, lst in self.end4.items():
            for x, bk, w in lst:
                ends.append((q, x, bk, w))
                byend[(bk, w)].add(('Z', q, x, bk, w))
        for (bk, w), zs in byend.items():
            s = (frozenset(zs), min(1, D))
            add('R', ('R', s), kE[w], ('R', start), (False, 0, bk))
            todo.append(s)
        pred = collections.defaultdict(set)
        if ROT:
            # F x the spelling of the element last read: a symbol
            # ((unit before, gap, unit after), d) follows only a symbol whose
            # unit after is its unit before (b_0's own state: any)
            for (q, x), q2 in self.fwd.items():
                ub, ua = x[0][0], x[0][2]
                if q == self.q0:
                    pred[((q2, ua), x)].add(q)
                else:
                    pred[((q2, ua), x)].add((q, ub))
        else:
            for (q, x), q2 in self.fwd.items():
                pred[(q2, x)].add(q)
        syms = sorted(set(x for (_, x) in self.fwd) | set(e[1] for e in ends))
        while todo:
            s = todo.pop()
            if s in rstates:
                continue
            rstates[s] = True
            S, c = s
            for x in syms:
                prev = set()
                for z in S:
                    if z[0] == 'Z':
                        if z[2] == x:
                            prev.add(z[1] if not ROT or z[1] == self.q0 else (z[1], x[0][0]))
                    else:
                        prev |= pred.get((z, x), set())
                if lg4.RNOQ0:
                    prev.discard(self.q0)
                if not prev:
                    continue
                p = (frozenset(prev), min(c + 1, D))
                add('R', ('R', p), kR[x[0]], ('R', s), (False, a, x[1]))
                todo.append(p)
        nfa.acc.add(('R', ('R', start)))
        self.nfa, self.foldmap, self.kL, self.kR, self.kE, self.kT = nfa, fold, kL, kR, kE, kT
        self.rstart = ('R', start)
        return nfa


def with_depth(lang, depth=DEPTH):
    """lang (a Lang4) rebuilt as a Lang4D"""
    l2 = Lang4D(lang.a, lang.unit, lang.fwd, lang.end4, lang.q0, lang.lfwd, lang.lstart,
                sorted(lang.seps, key=str), lends=lang.lends, unitL=lang.unitL,
                sepsL=lang.sepsL, psepsR=lang.psepsR, psepsL=lang.psepsL,
                lend_blank=lang.lend_blank)
    l2.depth = depth
    return l2
