"""Search for late instruction quasihalting with an accelerated simulator.

The simulator groups the tape into fixed blocks, stores equal blocks as runs,
moves across a whole run in one chain step, and proves reusable rules by
symbolic replay whenever a tape shape recurs.  Rules may use earlier rules,
and run lengths may be restricted to a residue class, so nested sweeps and
pair-consuming loops are covered.  Step counts are exact integers.

For each instruction the simulator keeps the step count at the end of the
last accelerated operation that fired it.  That is an upper bound for its
last firing so far.  A run ends when a rule or chain step provably repeats
for ever, when an undefined instruction is reached, or when a budget ends.

This is an untrusted search aid.  Its verdicts suggest where a late last
firing may or may not exist; only a Coq proof establishes a score or a bound.

`research/instruction-accel-hunt.tsv` records one sweep of the open
instruction families whose tape spans more than 100 cells after 10^7 steps
(`span_1e7`); families that reach an undefined instruction have one row per
`completion`.  `infinite` rows name the instructions of the repeating rule
(`recurring`) and the remaining fired ones (`quiet`) with `quiet_bound`, an
upper bound for their last firing.  `beyond_limit` rows passed the step
limit, and `unresolved` rows ran out of time; both depend on the budget.
"""
import argparse
import csv
from fractions import Fraction
import math
from math import comb
from pathlib import Path
import sys
import time

getattr(sys, 'set_int_max_str_digits', lambda n: None)(0)
INF = math.inf
NVAR = -2  # the number of applications of a rule
JVAR = -1  # summation index

def parse(text):
    tm = []
    for row in text.strip().split('_'):
        r = []
        for i in range(0, len(row), 3):
            c = row[i:i+3]
            if c[0] == '-' or c[2] not in 'AB': r.append(None)
            else: r.append((int(c[0]), 1 if c[1] == 'R' else 0, ord(c[2]) - 65))
        tm.append(r)
    return tm

class Lin:
    __slots__ = ('c', 'v')
    def __init__(self, c=0, v=None):
        self.c = c; self.v = v or {}
    def add(self, o):
        if o.__class__ is Lin:
            v = dict(self.v)
            for k, a in o.v.items():
                na = v.get(k, 0) + a
                if na: v[k] = na
                else: v.pop(k, None)
            return Lin(self.c + o.c, v)
        return Lin(self.c + o, self.v)
    def mul(self, n):
        if n == 0: return Lin(0)
        return Lin(self.c * n, {k: a * n for k, a in self.v.items()})
    def ev(self, vals):
        return self.c + sum(a * vals[k] for k, a in self.v.items())
    def comp(self, vals):
        """substitute variables by ints or Lins"""
        r = Lin(self.c)
        for k, a in self.v.items():
            x = vals[k]
            r = r.add(x.mul(a) if x.__class__ is Lin else x * a)
        return r
    def __repr__(self):
        return ' + '.join(['%d*x%d' % (a, k) for k, a in sorted(self.v.items())] + [str(self.c)])

def norm(e):
    if e.__class__ is Lin and not e.v: return e.c
    return e

def ladd(a, b):
    if a.__class__ is Lin: return norm(a.add(b))
    if b.__class__ is Lin: return norm(b.add(a))
    return a + b

class Poly:
    __slots__ = ('t',)
    def __init__(self, t=None): self.t = t or {}
    @staticmethod
    def const(c): return Poly({(): c} if c else {})
    @staticmethod
    def var(i): return Poly({((i, 1),): 1})
    @staticmethod
    def of(e):
        if e.__class__ is Poly: return e
        if e.__class__ is Lin:
            t = {((k, 1),): a for k, a in e.v.items() if a}
            if e.c: t[()] = e.c
            return Poly(t)
        return Poly.const(e)
    def add(self, o):
        t = dict(self.t)
        for m, c in o.t.items():
            n = t.get(m, 0) + c
            if n: t[m] = n
            else: t.pop(m, None)
        return Poly(t)
    def scale(self, c):
        if not c: return Poly()
        return Poly({m: a * c for m, a in self.t.items()})
    def mul(self, o):
        t = {}
        for m1, c1 in self.t.items():
            for m2, c2 in o.t.items():
                d = dict(m1)
                for v, e in m2: d[v] = d.get(v, 0) + e
                m = tuple(sorted(d.items()))
                n = t.get(m, 0) + c1 * c2
                if n: t[m] = n
                else: t.pop(m, None)
        return Poly(t)
    def pw(self, e):
        r = Poly.const(1)
        for _ in range(e): r = r.mul(self)
        return r
    def subst(self, mp):
        r = Poly()
        for m, c in self.t.items():
            term = Poly.const(c)
            for v, e in m:
                x = mp.get(v)
                term = term.mul((Poly.var(v) if x is None else x).pw(e))
            r = r.add(term)
        return r
    def ev(self, vals):
        s = 0
        for m, c in self.t.items():
            x = c
            for v, e in m: x = x * vals[v] ** e
            s += x
        if s.__class__ is Fraction:
            assert s.denominator == 1, 'non-integer step count'
            s = s.numerator
        return s
    def degree(self):
        return max((sum(e for _, e in m) for m in self.t), default=0)

_bern = [Fraction(1)]
def bern(n):
    while len(_bern) <= n:
        m = len(_bern)
        _bern.append(-sum(comb(m + 1, k) * _bern[k] for k in range(m)) / (m + 1))
    return _bern[n]
_faul = {}
def faulhaber(p):
    """sum_{j=0}^{N-1} j^p as Poly in NVAR"""
    if p not in _faul:
        t = {}
        for k in range(p + 1):
            c = Fraction(comb(p + 1, k)) * bern(k) / (p + 1)
            if c: t[((NVAR, p + 1 - k),)] = c
        _faul[p] = Poly(t)
    return _faul[p]

def sum_poly(P, deltas):
    """sum_{j=0}^{N-1} P(x + j*delta) as Poly over x and NVAR"""
    mp = {i: Poly({((i, 1),): 1, ((JVAR, 1),): d} if d else {((i, 1),): 1}) for i, d in enumerate(deltas)}
    Q = P.subst(mp)
    S = Poly()
    for m, c in Q.t.items():
        p = 0; rest = []
        for v, e in m:
            if v == JVAR: p = e
            else: rest.append((v, e))
        S = S.add(Poly({tuple(rest): c}).mul(faulhaber(p)))
    return S

class Rule:
    __slots__ = ('mins', 'varpos', 'deltas', 'finals', 'steps', 'mask', 'sump', 'lin', 'level', 'stride', 'resid', 'plain')

class Sim:
    def __init__(self, tm, k, prover=True, maxruns=60, maxdelta=3000, nested=True):
        self.tm = tm; self.k = k
        self.cache = {}
        self.left = [[0, INF]]; self.right = [[0, INF]]
        self.state = 0; self.dir = 1
        self.steps = 0; self.loops = 0
        self.last = {}; self.lastl = {}
        self.status = 'RUN'; self.infmask = 0
        self.prover = prover; self.maxruns = maxruns; self.maxdelta = maxdelta
        self.nested = nested
        self.rules = {}; self.past = {}; self.failed = {}
        self.nrules = 0; self.rule_apps = 0; self.maxlevel = 0
        self.haltslot = None
        self.maxbits = 10000
        self.inflevel = 0
        self.newkey_loop = 0; self.nkeys = 0; self.newrule_loop = 0

    def macro(self, sym, state, dr):
        key = (sym << 2) | (state << 1) | dr
        r = self.cache.get(key)
        if r is None:
            r = self.cache[key] = self._compute(sym, state, dr)
        return r

    def _compute(self, sym, state, dr):
        k = self.k; tm = self.tm
        cells = [(sym >> (2 * (k - 1 - i))) & 3 for i in range(k)]
        pos = 0 if dr == 1 else k - 1
        steps = 0; mask = 0
        limit = 2 * k * (4 ** k) * 2 + 16
        late = 0
        while 0 <= pos < k:
            slot = state * 4 + cells[pos]
            t = tm[state][cells[pos]]
            mask |= 1 << slot
            if t is None: return ('HALT', steps, mask, slot)
            if steps > limit:
                late |= 1 << slot
                if steps > 2 * limit: return ('LOOP', steps, mask, late)
            cells[pos] = t[0]; pos += 1 if t[1] else -1; state = t[2]
            steps += 1
        ns = 0
        for c in cells: ns = (ns << 2) | c
        return (ns, state, 1 if pos >= k else 0, steps, mask)

    def key(self):
        return (self.state, self.dir,
                tuple([b[0] * 2 + (b[1] == 1) for b in self.left]),
                tuple([b[0] * 2 + (b[1] == 1) for b in self.right]))

    def run(self, max_loops, deadline=None):
        left = self.left; right = self.right
        state = self.state; dr = self.dir
        steps = self.steps; loops = self.loops
        cache = self.cache; last = self.last; lastl = self.lastl
        prover = self.prover; maxruns = self.maxruns
        end = loops + max_loops
        while loops < end:
            loops += 1
            if (loops & 127) == 0:
                if deadline is not None and time.time() > deadline: break
                if steps.bit_length() > self.maxbits:
                    self.status = 'BIG'; break
            if prover and len(left) + len(right) <= maxruns:
                self.state = state; self.dir = dr; self.steps = steps; self.loops = loops
                res = self.try_prover()
                if res:
                    steps = self.steps
                    if self.status != 'RUN': break
                    continue
            if dr: stack = right; other = left
            else: stack = left; other = right
            top = stack[-1]
            r = cache.get((top[0] << 2) | (state << 1) | dr)
            if r is None: r = self.macro(top[0], state, dr)
            if r[0].__class__ is str:
                if r[0] == 'HALT':
                    steps += r[1]; last[r[2]] = steps
                    self.status = 'HALT'; self.haltslot = r[3]
                else:
                    self.status = 'INF_LOOP'; self.infmask = r[3]; last[r[2]] = steps
                break
            nsym, nstate, ndir, st, mask = r
            if nstate == state and ndir == dr:
                n = top[1]
                if n == INF:
                    self.status = 'INF_CHAIN'; self.infmask = mask
                    break
                stack.pop()
                steps += n * st
                if other[-1][0] == nsym: other[-1][1] += n
                else: other.append([nsym, n])
            else:
                if top[1] == 1: stack.pop()
                else: top[1] -= 1
                tgt = left if ndir else right
                if tgt[-1][0] == nsym: tgt[-1][1] += 1
                else: tgt.append([nsym, 1])
                state = nstate; dr = ndir
                steps += st
            last[mask] = steps; lastl[mask] = loops
        self.state = state; self.dir = dr; self.steps = steps; self.loops = loops

    # ---------------- prover ----------------
    def try_prover(self):
        key = self.key()
        rule = self.rules.get(key)
        if rule is not None:
            return self.apply(rule)
        pc = self.past.get(key)
        if pc is None:
            if len(self.past) > 200000: self.past.clear()
            self.past[key] = [self.loops, None]
            self.newkey_loop = self.loops; self.nkeys += 1
            return False
        delta = self.loops - pc[0]
        same = (pc[1] == delta)
        pc[0] = self.loops; pc[1] = delta
        if same and delta <= self.maxdelta and self.failed.get(key, 0) < 3:
            try:
                rule = self.prove(delta)
            except AssertionError:
                rule = None
            if rule is None:
                self.failed[key] = self.failed.get(key, 0) + 1
                return False
            self.rules[key] = rule; self.nrules += 1; self.newrule_loop = self.loops
            if rule.level > self.maxlevel: self.maxlevel = rule.level
            del self.past[key]
            return self.apply(rule)
        return False

    def prove(self, delta):
        mins = []; varpos = []; stride = []; resid = []; conc = []
        tapes = []
        for side, stack in ((0, self.left), (1, self.right)):
            s = []
            for idx, (sym, cnt) in enumerate(stack):
                if cnt == INF or cnt == 1: s.append([sym, cnt])
                else:
                    vi = len(mins); mins.append(1); varpos.append((side, idx))
                    stride.append(1); resid.append(0); conc.append(cnt)
                    s.append([sym, Lin(0, {vi: 1})])
            tapes.append(s)
        left, right = tapes
        stacks = (left, right)
        state = self.state; dr = self.dir
        box = [Poly()]   # steps
        rmask = 0; level = 1
        rules = self.rules if self.nested else None

        def lb(e):
            s = e.c
            for k, a in e.v.items():
                if a < 0: return None
                s += a * mins[k]
            return s
        def ensure(e, need):
            cur = lb(e)
            if cur is None: return False
            if cur >= need: return True
            if not e.v: return False
            kk = next(iter(e.v)); a = e.v[kk]
            mins[kk] += -((cur - need) // a)
            return True
        def restrict(k, d):
            """re-parametrize y_k = d*z + rho (rho from the concrete value)"""
            rho = conc[k] % d
            for st in stacks:
                for b in st:
                    e = b[1]
                    if e.__class__ is Lin and k in e.v:
                        a = e.v[k]
                        v = dict(e.v); v[k] = a * d
                        b[1] = Lin(e.c + a * rho, v)
            box[0] = box[0].subst({k: Poly({((k, 1),): d, (): rho} if rho else {((k, 1),): d})})
            mins[k] = max(0, -((rho - mins[k]) // d))
            resid[k] += stride[k] * rho; stride[k] *= d
            conc[k] = (conc[k] - rho) // d
        def divisible(e, d):
            """restrict variables so every coefficient of Lin e is divisible by d; True if anything changed"""
            ch = False
            for k, a in list(e.v.items()):
                g = math.gcd(a, d)
                if d // g > 1:
                    restrict(k, d // g); ch = True
            return ch

        def sym_apply(rule):
            """0: not applicable, 1: applied, None: proof fails"""
            nonlocal rmask, level
            for _guard in range(50):
                again = False
                ys = []
                for idx, (s, i) in enumerate(rule.varpos):
                    v = stacks[s][i][1]; st = rule.stride[idx]; rs = rule.resid[idx]
                    if v.__class__ is Lin:
                        if st > 1:
                            if divisible(v, st): again = True; break
                            if (v.c - rs) % st: return 0
                            y = norm(Lin((v.c - rs) // st, {k: a // st for k, a in v.v.items()}))
                        else: y = v
                    else:
                        q, r = divmod(v - rs, st)
                        if r: return 0
                        y = q
                    ys.append(y)
                if again: continue
                for y, m in zip(ys, rule.mins):
                    if y.__class__ is Lin:
                        if not ensure(y, m): return None
                    elif y < m: return 0
                if rule.deltas is not None:
                    nc = None; nsyms = []
                    for y, m, d in zip(ys, rule.mins, rule.deltas):
                        if d < 0:
                            if y.__class__ is Lin:
                                e = y.add(-m)
                                D = -d
                                if D > 1:
                                    if divisible(e, D): again = True; break
                                    r = e.c % D
                                    nsyms.append(Lin((e.c - r) // D + 1, {k: a // D for k, a in e.v.items()}))
                                else:
                                    nsyms.append(e.add(1))
                            else:
                                ni = (y - m) // (-d) + 1
                                if nc is None or ni < nc: nc = ni
                    if again: continue
                    if nc is None and not nsyms: return None
                    if nc is not None:
                        for e in nsyms:
                            if not ensure(e, nc): return None
                        n = nc
                    else:
                        if len(nsyms) != 1: return None
                        n = nsyms[0]
                    mp = {i: Poly.of(y) for i, y in enumerate(ys)}
                    mp[NVAR] = Poly.of(n)
                    box[0] = box[0].add(rule.sump.subst(mp))
                    for idx, ((s, i), d) in enumerate(zip(rule.varpos, rule.deltas)):
                        if d:
                            dd = d * rule.stride[idx]
                            nd = n.mul(dd) if n.__class__ is Lin else n * dd
                            stacks[s][i][1] = ladd(stacks[s][i][1], nd)
                else:
                    newvals = [norm(f.comp(ys)) for f in rule.finals]
                    for nv in newvals:
                        if nv.__class__ is Lin:
                            if not ensure(nv, 1): return None
                        elif nv < 1: return None
                    mp = {i: Poly.of(y) for i, y in enumerate(ys)}
                    box[0] = box[0].add(rule.steps.subst(mp))
                    for (s, i), nv in zip(rule.varpos, newvals):
                        stacks[s][i][1] = nv
                rmask |= rule.mask
                if rule.level + 1 > level: level = rule.level + 1
                return 1
            return None

        for _ in range(delta):
            if rules:
                key = (state, dr,
                       tuple([b[0] * 2 + (b[1].__class__ is int and b[1] == 1) for b in left]),
                       tuple([b[0] * 2 + (b[1].__class__ is int and b[1] == 1) for b in right]))
                rule = rules.get(key)
                if rule is not None:
                    res = sym_apply(rule)
                    if res is None: return None
                    if res: continue
            if dr: stack = right; other = left
            else: stack = left; other = right
            top = stack[-1]
            r = self.macro(top[0], state, dr)
            if r[0].__class__ is str: return None
            nsym, nstate, ndir, st, mask = r
            rmask |= mask
            cnt = top[1]
            if nstate == state and ndir == dr:
                if cnt == INF: return None
                stack.pop()
                box[0] = box[0].add(Poly.of(cnt).scale(st))
                o = other[-1]
                if o[0] == nsym:
                    if o[1] != INF: o[1] = ladd(o[1], cnt)
                else: other.append([nsym, cnt])
            else:
                if cnt.__class__ is Lin:
                    if not ensure(cnt, 2): return None
                    top[1] = cnt.add(-1)
                elif cnt == 1: stack.pop()
                else: top[1] = cnt - 1
                tgt = left if ndir else right
                o = tgt[-1]
                if o[0] == nsym:
                    if o[1] != INF: o[1] = ladd(o[1], 1)
                else: tgt.append([nsym, 1])
                state = nstate; dr = ndir
                box[0] = box[0].add(Poly.const(st))
        steps = box[0]
        if state != self.state or dr != self.dir: return None
        if len(left) != len(self.left) or len(right) != len(self.right): return None
        finals = [None] * len(mins)
        vi = 0
        for sym_stack, orig in ((left, self.left), (right, self.right)):
            for idx in range(len(orig)):
                if sym_stack[idx][0] != orig[idx][0]: return None
                oc = orig[idx][1]; fc = sym_stack[idx][1]
                if oc == INF or oc == 1:
                    if fc.__class__ is Lin or fc != oc: return None
                else:
                    finals[vi] = fc if fc.__class__ is Lin else Lin(fc)
                    vi += 1
        deltas = []
        diff = True
        for i, f in enumerate(finals):
            if len(f.v) == 1 and f.v.get(i) == stride[i] and (f.c - resid[i]) % stride[i] == 0:
                deltas.append((f.c - resid[i]) // stride[i])
            else: diff = False; break
        for f in finals:
            for a in f.v.values():
                if a < 0: return None
        # the concrete configuration must itself satisfy the rule's parametrization
        R = Rule()
        R.mins = mins; R.varpos = varpos; R.deltas = deltas if diff else None
        R.stride = stride; R.resid = resid; R.plain = all(s == 1 for s in stride)
        R.finals = finals; R.steps = steps; R.mask = rmask; R.level = level
        R.sump = sum_poly(steps, deltas) if diff else None
        R.lin = None
        if diff and steps.degree() <= 1 and all(c.__class__ is int for c in steps.t.values()):
            c0 = steps.t.get((), 0)
            co = {m[0][0]: c for m, c in steps.t.items() if m}
            R.lin = (c0, co, sum(c * deltas[k] for k, c in co.items()))
        return R

    def apply(self, rule):
        stacks = (self.left, self.right)
        if rule.plain:
            vals = [stacks[s][i][1] for s, i in rule.varpos]
        else:
            vals = []
            for (s, i), st, rs in zip(rule.varpos, rule.stride, rule.resid):
                q, r = divmod(stacks[s][i][1] - rs, st)
                if r: return False
                vals.append(q)
        for v, m in zip(vals, rule.mins):
            if v < m: return False
        deltas = rule.deltas
        if deltas is not None:
            n = None
            for v, m, d in zip(vals, rule.mins, deltas):
                if d < 0:
                    ni = (v - m) // (-d) + 1
                    if n is None or ni < n: n = ni
            if n is None:
                self.status = 'INF_RULE'; self.infmask = rule.mask; self.inflevel = rule.level
                return True
            if rule.lin is not None:
                c0, co, slope = rule.lin
                l0 = c0 + sum(c * vals[k] for k, c in co.items())
                self.steps += n * l0 + slope * (n * (n - 1) // 2)
            else:
                d = {i: v for i, v in enumerate(vals)}; d[NVAR] = n
                self.steps += rule.sump.ev(d)
            for (s, i), dl, st in zip(rule.varpos, deltas, rule.stride):
                stacks[s][i][1] += n * dl * st
        else:
            newvals = [f.ev(vals) for f in rule.finals]
            for nv in newvals:
                if nv < 1: return False
            if rule.plain and all(nv >= v for nv, v in zip(newvals, vals)):
                self.status = 'INF_RULE'; self.infmask = rule.mask; self.inflevel = rule.level
                return True
            self.steps += rule.steps.ev(vals)
            for (s, i), nv in zip(rule.varpos, newvals):
                stacks[s][i][1] = nv
        self.rule_apps += 1
        self.last[rule.mask] = self.steps; self.lastl[rule.mask] = self.loops
        return True

def slot_last(sim):
    out = [0] * 8
    for mask, t in sim.last.items():
        for s in range(8):
            if mask >> s & 1 and t > out[s]: out[s] = t
    return out

def periods(tm, steps=60000):
    """Short tape periods seen after a direct run; used to pick block sizes."""
    tape = bytearray(2 * steps + 3); pos = steps + 1; st = 0; lo = hi = pos
    for _ in range(steps):
        t = tm[st][tape[pos]]
        if t is None: break
        tape[pos] = t[0]; pos += 1 if t[1] else -1; st = t[2]
        if pos < lo: lo = pos
        elif pos > hi: hi = pos
    seg = bytes(tape[lo:hi + 1]); n = len(seg)
    if n < 40: return []
    good = [p for p in range(1, 17)
            if sum(1 for i in range(n - p) if seg[i] == seg[i + p]) > 0.85 * (n - p)]
    out = []
    for p in good:
        if not any(p % q == 0 for q in out): out.append(p)
    return out


def analyze(text, budget=2.0, blocks=None, maxruns=60, maxbits=10000):
    """Try several block sizes for equal time, then continue the best one."""
    tm = parse(text)
    if blocks is None:
        blocks = [1, 2, 3, 4, 6]
        for p in periods(tm):
            for k in (p, 2 * p):
                if k <= 16 and k not in blocks: blocks.append(k)
    best = None
    start = time.time()
    share = budget / (2 * len(blocks))
    for k in blocks:
        sim = Sim(tm, k, maxruns=maxruns)
        sim.maxbits = maxbits
        sim.run(10**12, deadline=time.time() + share)
        score = (sim.status != 'RUN', sim.steps)
        if best is None or score > best[0]: best = (score, k, sim)
        if sim.status != 'RUN': break
    _, k, sim = best
    if sim.status == 'RUN':
        sim.run(10**12, deadline=start + budget)
    return k, sim


NAMES = ['A0', 'A1', 'A2', 'A3', 'B0', 'B1', 'B2', 'B3']
VERDICT = {'INF_RULE': 'infinite', 'INF_CHAIN': 'infinite', 'INF_LOOP': 'infinite',
           'HALT': 'undefined_reached', 'BIG': 'beyond_limit', 'RUN': 'unresolved'}
FIELDS = ['machine', 'verdict', 'block', 'log10_steps', 'rule_level', 'recurring',
          'quiet', 'quiet_bound']


def log10(n):
    if n <= 0: return 0.0
    digits = str(n)
    return len(digits) - 1 + math.log10(int(digits[:15]) / 10 ** (len(digits[:15]) - 1))


def row(text, k, sim):
    """One ledger row.  `quiet_bound` is exact only up to the last operation."""
    last = slot_last(sim)
    final = sim.status.startswith('INF')
    recurring = [NAMES[s] for s in range(8) if sim.infmask >> s & 1] if final else []
    quiet = [s for s in range(8) if last[s] and NAMES[s] not in recurring] if final else []
    return {'machine': text, 'verdict': VERDICT[sim.status], 'block': k,
            'log10_steps': '%.1f' % log10(sim.steps), 'rule_level': sim.maxlevel,
            'recurring': ','.join(recurring), 'quiet': ','.join(NAMES[s] for s in quiet),
            'quiet_bound': max((last[s] for s in quiet), default='') if final else ''}


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--machine', action='append', default=[],
                        help='program text; may be repeated')
    parser.add_argument('--input', type=Path,
                        help='file whose first tab-separated column is a program')
    parser.add_argument('--budget', type=float, default=2.0, help='seconds per program')
    parser.add_argument('--block', type=int, action='append',
                        help='block size to try; default tries 1,2,3,4,6 and tape periods')
    parser.add_argument('--max-runs', type=int, default=60,
                        help='largest tape, in runs, on which rules are attempted')
    parser.add_argument('--max-bits', type=int, default=10000,
                        help='stop once the step count has this many bits')
    args = parser.parse_args()
    machines = list(args.machine)
    if args.input:
        machines += [line.split('\t')[0].strip() for line in args.input.read_text().splitlines()]
    out = csv.DictWriter(sys.stdout, FIELDS, delimiter='\t', lineterminator='\n')
    out.writeheader()
    for text in machines:
        if len(text) != 25 or text == 'machine': continue
        k, sim = analyze(text, args.budget, args.block, args.max_runs, args.max_bits)
        out.writerow(row(text, k, sim))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
