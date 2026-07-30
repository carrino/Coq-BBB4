#!/usr/bin/env python3
"""UNTRUSTED ladder engine: symbolic block-RLE replay with rules-as-data.

Stage A of docs/LADDER_PLAN.md.  Configurations are BLOCK run-length
encodings -- runs are (word, count) with word a primitive cell tuple --
with AFFINE symbolic counts.  Engine ops: concrete step, chain hop over
uniform runs, and bulk rule application (drain one coordinate per
application).  The rung-two addition: a rule's symbolic replay may APPLY
previously proven rules, so higher rules are built out of lower ones --
block crossings, carries and inner drains are DISCOVERED rules, not
primitives.

Nothing here carries proof weight; a ladder found here is a certificate
candidate for the Stage-B checker.

Conventions
  * config = (q, h, L, R): state, head symbol, half-tapes as tuples of
    (word, Expr) runs nearest-first, trailing blanks implicit.  A word is a
    tuple of cell symbols, len >= 1, primitive (not a power), non-uniform
    unless len == 1.  Reading a side outward spells word repeated count
    times, run after run.
  * Expr is affine: const + sum coeff_i * var_i; provable bounds use var
    lower bounds (lbs), sound only through nonnegative coefficients.
"""


# ---------------------------------------------------------------- expressions

class Expr:
    __slots__ = ('c', 'v')

    def __init__(self, c=0, v=None):
        self.c = c
        self.v = dict(v) if v else {}
        for k in [k for k, x in self.v.items() if x == 0]:
            del self.v[k]

    @staticmethod
    def of(x):
        return x if isinstance(x, Expr) else Expr(x)

    def __add__(self, o):
        o = Expr.of(o)
        v = dict(self.v)
        for k, x in o.v.items():
            v[k] = v.get(k, 0) + x
        return Expr(self.c + o.c, v)

    def __sub__(self, o):
        o = Expr.of(o)
        return self + Expr(-o.c, {k: -x for k, x in o.v.items()})

    def scale(self, n):
        return Expr(self.c * n, {k: x * n for k, x in self.v.items()})

    def __eq__(self, o):
        o = Expr.of(o)
        return self.c == o.c and self.v == o.v

    def __hash__(self):
        return hash((self.c, tuple(sorted(self.v.items()))))

    def is_const(self):
        return not self.v

    def min_val(self, lbs):
        m = self.c
        for k, x in self.v.items():
            if x >= 0:
                m += x * lbs.get(k, 1)
            else:
                return None
        return m

    def subst(self, env):
        e = Expr(self.c)
        for k, x in self.v.items():
            if k in env:
                e = e + Expr.of(env[k]).scale(x)
            else:
                e = e + Expr(0, {k: x})
        return e

    def __repr__(self):
        parts = [str(self.c)] if self.c or not self.v else []
        for k, x in sorted(self.v.items()):
            parts.append(('%s' if x == 1 else str(x) + '*%s') % k)
        return '+'.join(parts) or '0'


# ------------------------------------------------------------------- machines

def parse_tm(spec):
    tm = {}
    for q, part in enumerate(spec.strip().split('_')):
        for s in range(len(part) // 3):
            e = part[3 * s:3 * s + 3]
            if e[0] == '-' or e[2] in 'ZH-':
                tm[(q, s)] = None
            else:
                tm[(q, s)] = (int(e[0]), +1 if e[1] == 'R' else -1,
                              ord(e[2]) - ord('A'))
    return tm


def n_states(tm):
    return 1 + max(q for q, _ in tm)


MARKER = ('#',)      # abstract rest-of-side in LOCAL rules


# -------------------------------------------------------------------- words

def primitive(w):
    """Primitive root of a word."""
    n = len(w)
    for p in range(1, n):
        if n % p == 0 and w == w[:p] * (n // p):
            return w[:p]
    return w


def canon_run(w, e):
    """Canonicalize a run: primitive word; uniform words collapse to len 1."""
    if len(set(w)) == 1:
        return ((w[0],), e.scale(len(w)) if len(w) > 1 else e)
    p = primitive(w)
    if len(p) < len(w):
        return (p, e.scale(len(w) // len(p)))
    return (w, e)


# ------------------------------------------------------------------- configs

def norm_side(runs, lbs):
    """Canonicalize runs, drop zero runs, merge equal-word neighbors, absorb
    explicit cells into adjacent block runs, strip far blanks."""
    # 1. canonicalize + drop zeros
    rs = []
    for w, e in runs:
        if e.is_const() and e.c == 0:
            continue
        w, e = canon_run(tuple(w), e)
        rs.append((w, e))
    # 2. absorb / merge, in a fixpoint loop (cheap: lists are short)
    changed = True
    while changed:
        changed = False
        out = []
        i = 0
        while i < len(rs):
            w, e = rs[i]
            if out:
                pw, pe = out[-1]
                # merge equal words
                if pw == w:
                    out[-1] = (w, pe + e)
                    i += 1
                    changed = True
                    continue
                # explicit cells before a block: fold |w| unit cells that
                # spell w's END... (cells nearer head come first; the block
                # continues outward).  Handled in the unit-into-block case
                # below only when the previous run is a concrete unit-run
                # covering exactly a full copy adjacent to the block.
                if (len(w) > 1 and len(pw) == 1 and pe.is_const()
                        and pe.c >= 1):
                    # try to peel one copy of w off the unit-run boundary:
                    # cells outward: [pw]*pe.c then w^e.  The last cells of
                    # the unit segment adjacent to w^e would need to equal a
                    # suffix of nothing -- only a FULL uniform copy works,
                    # i.e. w uniform, but uniform words are len 1.  Skip.
                    pass
                # unit cells after a block run that extend it: previous is
                # block (len>1), current is units spelling w[0:...]: fold
                # only full copies: current unit run (s,n) with w == (s,)*k
                # impossible (w non-uniform).  Multi-run fold handled below.
            out.append((w, e))
            i += 1
        rs = out
        # 3. multi-run fold: a maximal stretch of CONCRETE unit runs spelling
        # exactly one copy of an adjacent block word folds into the block.
        rs2 = []
        i = 0
        while i < len(rs):
            # try fold: unit-run stretch [i..j) followed by block run
            j = i
            cells = []
            while (j < len(rs) and len(rs[j][0]) == 1
                   and rs[j][0] != MARKER and rs[j][1].is_const()
                   and rs[j][1].c <= 8 and len(cells) <= 8):
                cells.extend([rs[j][0][0]] * rs[j][1].c)
                j += 1
            if (j < len(rs) and len(rs[j][0]) > 1 and cells
                    and len(cells) >= len(rs[j][0])):
                w = rs[j][0]
                k = len(w)
                if tuple(cells[-k:]) == w:
                    # fold the last copy into the block; re-emit remaining
                    # cells as unit runs
                    rest = cells[:-k]
                    for s in rest:
                        rs2.append(((s,), Expr(1)))
                    rs2.append((w, rs[j][1] + Expr(1)))
                    i = j + 1
                    changed = True
                    continue
            # or: block run followed by unit cells spelling a copy (outward
            # continuation)
            if (len(rs[i][0]) > 1 and i + 1 < len(rs)):
                w = rs[i][0]
                k = len(w)
                jj = i + 1
                cells = []
                while (jj < len(rs) and len(rs[jj][0]) == 1
                       and rs[jj][0] != MARKER
                       and rs[jj][1].is_const() and rs[jj][1].c <= 8
                       and len(cells) <= k):
                    cells.extend([rs[jj][0][0]] * rs[jj][1].c)
                    jj += 1
                if len(cells) >= k and tuple(cells[:k]) == w:
                    rs2.append((w, rs[i][1] + Expr(1)))
                    for s in cells[k:]:
                        rs2.append(((s,), Expr(1)))
                    i = jj
                    changed = True
                    continue
            rs2.append(rs[i])
            i += 1
        rs = rs2
        # re-merge after folds
        out = []
        for w, e in rs:
            if out and out[-1][0] == w:
                out[-1] = (w, out[-1][1] + e)
            else:
                out.append((w, e))
        rs = out
    # 4. strip far blanks
    while rs and set(rs[-1][0]) == {0}:
        rs.pop()
    return tuple(rs)


def cfg_key(cfg):
    q, h, L, R = cfg
    return (q, h, tuple(w for w, _ in L), tuple(w for w, _ in R))


def cfg_counts(cfg):
    _, _, L, R = cfg
    return tuple(e for _, e in L) + tuple(e for _, e in R)


def cfg_with_counts(cfg, counts):
    q, h, L, R = cfg
    nl = len(L)
    L2 = tuple((L[i][0], counts[i]) for i in range(nl))
    R2 = tuple((R[i][0], counts[nl + i]) for i in range(len(R)))
    return (q, h, L2, R2)


def cfg_repr(cfg):
    q, h, L, R = cfg
    def side(runs):
        return ' '.join('%s^%r' % (''.join(map(str, w)), e) for w, e in runs)
    return '%s[%d] L<%s> R<%s>' % (chr(65 + q), h, side(L), side(R))


# --------------------------------------------------------------------- rules

class Rule:
    __slots__ = ('name', 'lhs', 'rhs', 'lbs', 'dec', 'fired', 'level')

    def __init__(self, name, lhs, rhs, lbs, dec, fired, level):
        self.name, self.lhs, self.rhs = name, lhs, rhs
        self.lbs, self.dec, self.fired, self.level = lbs, dec, fired, level

    def __repr__(self):
        return '<%s L%d %s => %s | lbs %s>' % (
            self.name, self.level, cfg_repr(self.lhs), cfg_repr(self.rhs),
            self.lbs)


def _match_side(pat_runs, got_runs, env):
    """Match one side; MARKER as the last pattern run binds the remainder.
    Returns rest tuple (or () for exact match), or None."""
    local = pat_runs and pat_runs[-1][0] == MARKER
    pats = pat_runs[:-1] if local else pat_runs
    if local:
        if len(got_runs) < len(pats):
            return None
    elif len(got_runs) != len(pats):
        return None
    for (pw, pe), (gw, ge) in zip(pats, got_runs):
        if pw != gw:
            return None
        if pe.is_const():
            if not (ge.is_const() and ge.c == pe.c):
                return None
        else:
            items = list(pe.v.items())
            if len(items) != 1 or items[0][1] != 1:
                return None
            var = items[0][0]
            need = ge - Expr(pe.c)
            if var in env:
                if env[var] != need:
                    return None
            else:
                env[var] = need
    return got_runs[len(pats):] if local else ()


def match_rule(rule, cfg):
    """Returns (env, restL, restR) or None."""
    q, h, L, R = cfg
    lq, lh, lL, lR = rule.lhs
    if (q, h) != (lq, lh):
        return None
    env = {}
    restL = _match_side(lL, L, env)
    if restL is None:
        return None
    restR = _match_side(lR, R, env)
    if restR is None:
        return None
    return env, restL, restR


# -------------------------------------------------------------------- engine

class Replay:
    def __init__(self, tm, rules, lbs=None, budget=400, raise_ok=True):
        self.tm = tm
        self.rules = rules
        self.lbs = dict(lbs or {})
        self.budget = budget
        self.raise_ok = raise_ok
        self.fired = {}
        self.trace = []
        self.fail = None

    def _fire(self, tr, mult):
        self.fired[tr] = self.fired.get(tr, Expr(0)) + Expr.of(mult)

    def _need_ge1(self, e):
        m = e.min_val(self.lbs)
        if m is not None and m >= 1:
            return True
        if not self.raise_ok:
            return False
        best = None
        for k, x in e.v.items():
            if x > 0:
                best = k
                break
        if best is None:
            return False
        rest = Expr(e.c, {k: x for k, x in e.v.items() if k != best})
        rm = rest.min_val(self.lbs)
        if rm is None:
            return False
        need = 1 - rm
        x = e.v[best]
        lb = -(-need // x)
        if lb > self.lbs.get(best, 1):
            self.lbs[best] = lb
        return True

    def _pop_cell(self, side):
        """Pop one cell; multi-cell words shed their first cell, the rest of
        the copy becomes explicit unit runs.  Returns (sym, runs) or None.
        Popping the abstract-rest marker fails: a local rule's replay may not
        look past its window."""
        if not side:
            return (0, side)
        w, e = side[0]
        if w == MARKER:
            return None
        if not self._need_ge1(e):
            return None
        e1 = e - Expr(1)
        rest_units = tuple(((s,), Expr(1)) for s in w[1:])
        if e1.is_const() and e1.c == 0:
            return (w[0], rest_units + side[1:])
        m1 = e1.min_val(self.lbs)
        if m1 is None or m1 < 0:
            if not self._need_ge1(e1):
                return None
        return (w[0], rest_units + ((w, e1),) + side[1:])

    def _push_cell(self, side, sym):
        return (((sym,), Expr(1)),) + side

    def step(self, cfg):
        q, h, L, R = cfg
        t = self.tm.get((q, h))
        if t is None:
            self.fail = 'halt'
            return None
        w, d, q2 = t
        self._fire((q, h), 1)
        if d > 0:
            L2 = self._push_cell(L, w)
            pop = self._pop_cell(R)
            if pop is None:
                self.fail = 'pop'
                return None
            h2, R2 = pop
            return (q2, h2, norm_side(L2, self.lbs), norm_side(R2, self.lbs))
        else:
            R2 = self._push_cell(R, w)
            pop = self._pop_cell(L)
            if pop is None:
                self.fail = 'pop'
                return None
            h2, L2 = pop
            return (q2, h2, norm_side(L2, self.lbs), norm_side(R2, self.lbs))

    def chain(self, cfg):
        """Uniform-run chain hop (words of length 1 only; block crossings are
        discovered rules, not primitives)."""
        q, h, L, R = cfg
        t = self.tm.get((q, h))
        if t is None:
            return None
        w, d, q2 = t
        if q2 != q:
            return None
        side = R if d > 0 else L
        if not side or len(side[0][0]) != 1 or side[0][0][0] != h:
            return None
        e = side[0][1]
        if not self._need_ge1(e):
            return None
        self._fire((q, h), e + Expr(1))
        rest = side[1:]
        crossed = ((w,), e + Expr(1))
        if d > 0:
            L2 = norm_side((crossed,) + L, self.lbs)
            pop = self._pop_cell(rest)
            if pop is None:
                self.fail = 'pop'
                return None
            h2, R2 = pop
            return (q, h2, L2, norm_side(R2, self.lbs))
        else:
            R2 = norm_side((crossed,) + R, self.lbs)
            pop = self._pop_cell(rest)
            if pop is None:
                self.fail = 'pop'
                return None
            h2, L2 = pop
            return (q, h2, norm_side(L2, self.lbs), R2)

    def apply_rule(self, rule, cfg, bulk=True):
        m = match_rule(rule, cfg)
        if m is None:
            return None
        env, restL, restR = m
        for var, e in env.items():
            need = rule.lbs.get(var, 1)
            m = e.min_val(self.lbs)
            if m is None or m < need:
                ok = False
                if self.raise_ok and not e.is_const():
                    ok = self._need_ge1(e - Expr(need - 1))
                if not ok:
                    return None
        counts_l = cfg_counts(rule.lhs)
        counts_r = cfg_counts(rule.rhs)
        if rule.dec is None or not bulk:
            reps = Expr(1)
            out_counts = [e.subst(env) for e in counts_r]
        else:
            dvar = list(counts_l[rule.dec].v)[0]
            lb = rule.lbs.get(dvar, 1)
            e_dec = env[dvar]
            reps = e_dec - Expr(lb - 1)
            if not self._need_ge1(reps):
                return None
            out_counts = []
            for el, er in zip(counts_l, counts_r):
                d = er - el
                if not d.is_const():
                    return None
                base = el.subst(env)
                out_counts.append(base + reps.scale(d.c) if d.c else base)
        for tr in rule.fired:
            self._fire(tr, reps)      # under-approximation: >= reps firings
        out = cfg_with_counts(rule.rhs, out_counts)
        q, h, L, R = out
        # splice abstract rests back in place of the markers
        if L and L[-1][0] == MARKER:
            L = L[:-1] + restL
        if R and R[-1][0] == MARKER:
            R = R[:-1] + restR
        return (q, h, norm_side(L, self.lbs), norm_side(R, self.lbs))

    def run(self, cfg, target=None):
        max_runs = len(cfg[2]) + len(cfg[3]) + 10
        for _ in range(self.budget):
            if target is not None and cfg == target:
                return cfg
            if len(cfg[2]) + len(cfg[3]) > max_runs:
                self.fail = 'wander'
                return None
            nxt = None
            for rule in self.rules:
                nxt = self.apply_rule(rule, cfg)
                if nxt is not None:
                    self.trace.append(('rule', rule.name))
                    break
            if nxt is None:
                nxt = self.chain(cfg)
                if nxt is not None:
                    self.trace.append(('chain',))
            if nxt is None:
                nxt = self.step(cfg)
                if nxt is not None:
                    self.trace.append(('step',))
            if nxt is None:
                return None
            cfg = nxt
        self.fail = 'budget'
        return None
