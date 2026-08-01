#!/usr/bin/env python3
"""UNTRUSTED rung two: the VALUE-INDEXED RULE FAMILY.

The local-rule layer (discover.py) proves context-free rules behind a wall
marker.  It does not close, and RULE_LADDER.md sec.3 says why: an octave
meta-cycle is 2^k rests whose mid-octave shapes track the bit pattern, so no
fixed-shape anchor with an affine self-map exists.  The fix is not a bigger
shape vocabulary, it is a different KIND of tape item:

    CTR(alph, v) -- a counter segment denoting the ENCODED VALUE v,

with the machine's increment stated as a RULE FAMILY over the carry index j
rather than as one rule per shape:

    interior   E(v) ->+ E(v+1)   for v whose digit string ends in j set digits
                                 followed by a clear one; the j set digits are
                                 drained by ONE BULK application of a proven
                                 ladder rule, so j is symbolic;
    overflow   E(p, b^p-1) ->+ E(p', c)   the fill: the counter WIDENS, and
                                 this is the only arm that moves the width.

The width p is the family's SECOND PARAMETER, and the fill law -- what the
top string of width p goes to -- is INFERRED, never assumed (`Fill`).  It used
to be hard-coded as the odometer carry `[0]*p ++ [1]`, and every machine that
does something else (widen by two, reset to zero, land on a fixed low string)
read as "overflow leaves the family" against an assumption rather than against
its own behaviour.

Every (p, v) takes exactly one arm, so the family is closed by construction,
and the arms plus a concrete boot are a never-QH certificate CANDIDATE.

The alphabet is NOT curated.  It is read off the ladder: the block words the
ladder's own carry rules DRAIN are the digits (up to phase, i.e. rotation),
and the digit-value assignment is fixed by requiring that consecutive anchor
visits differ by exactly +1.  If no ladder rule names a digit, the family is
rejected -- there is no fallback alphabet list to be blind to.

Nothing here carries proof weight.
"""

import itertools
import json
import time
from collections import Counter, defaultdict

from engine import (Expr, MARKER, Replay, Rule, canon_run, cfg_counts,
                    cfg_repr, match_rule, n_states, parse_tm)
from trace import block_rle, simulate
from validate import raw_run


# ------------------------------------------------------------------ helpers

def runs_cells(runs, env=None):
    """Concrete cell list of a side, or None if symbolic / has a marker."""
    out = []
    for w, e in runs:
        if w == MARKER:
            return None
        n = e.subst(env or {})
        if not n.is_const() or n.c < 0:
            return None
        out.extend(list(w) * n.c)
    while out and out[-1] == 0:
        out.pop()
    return out


def cfg_cells(cfg, env=None):
    q, h, L, R = cfg
    lc, rc = runs_cells(L, env), runs_cells(R, env)
    if lc is None or rc is None:
        return None
    return (q, h, tuple(lc), tuple(rc))


def rots(w):
    return {w[i:] + w[:i] for i in range(len(w))}


# --------------------------------------------------------------- the CODE
# Two ways a counter segment can denote a number.  `binary` is positional.
# `gray` is the REFLECTED code, whose successive words differ in a single
# digit -- which is why "count up to full, then back down to zero, then widen"
# is what it looks like on the tape, and why a positional reader sees the value
# jump and files the machine under `no counter reading at any anchor`.
# Generalized to base b: decode is the running sum from the most significant
# digit down, encode is the difference to the next digit up; at b = 2 both
# collapse to the XOR chain.  Digit strings are LSB-first, so index 0 is least
# significant.

def gray_decode(ds, b):
    out, s = [], 0
    for d in reversed(ds):
        s = (s + d) % b
        out.append(s)
    return out[::-1]


def gray_encode(ns, b):
    return [(ns[i] - (ns[i + 1] if i + 1 < len(ns) else 0)) % b
            for i in range(len(ns))]


def digit_words(rules):
    """The words the ladder moves ONE OF per application -- the digits, named
    by the ladder itself.

    A carry rule consumes (or lays down) exactly one digit each time it fires,
    so any run coordinate whose count changes by exactly +-1 carries a digit
    word, up to phase -- the rule may have been discovered with the head
    mid-digit, so rotations count too.  Usually a block word (10 and 01 on the
    dev fixture); a single cell when the machine's digits are one cell wide.
    Both directions matter: the fixture's carry DRAINS its digit blocks while
    the bounded-carrier row BUILDS them, and reading only drains makes the
    searcher blind to half the population.  This is the whole of the alphabet
    inference -- there is no curated list to be blind to."""
    out = {}
    for ru in rules:
        runs = ru.lhs[2] + ru.lhs[3]
        cl, cr = cfg_counts(ru.lhs), cfg_counts(ru.rhs)
        for i, (w, _) in enumerate(runs):
            if w == MARKER:
                continue
            d = cr[i] - cl[i]
            if d.is_const() and abs(d.c) == 1:
                out.setdefault(w, ru.name)
    return out


# --------------------------------------------------------- the NUMERATION
# `Fam.decode` used to sum `d_i * b**i`, full stop.  That is ONE number
# system, and a machine counting in another (Fibonacci rank, a redundant base
# over cell pairs) reads as `no +1 chain` against the assumption rather than
# against its own behaviour -- the same error the carry (4e), the anchor, the
# terminator (4f) and the code (4g) each were until they became parameters.
# So the weight sequence is read off the machine too:
#
#   `fit_weights`  -- inside a width class, take the distinct strings in order
#                     of FIRST APPEARANCE and require Sum (d' - d) . w = step
#                     between consecutive ranks.  Exact rational elimination,
#                     equations added greedily, contradictions COUNTED rather
#                     than averaged away.  Differences and not absolute ranks,
#                     because a class whose top digit is pinned carries a
#                     per-width offset and an absolute fit would solve it away
#                     by setting the top weight to zero.
#   `fit_classes`  -- the CANONICAL form, which is what a weight sequence
#                     actually costs.  The representation is not unique
#                     (Fibonacci: 1100 and 0100 are both 2) and the machine
#                     writes exactly one of them, so `of_value` has to produce
#                     the machine's string.  The canonical set is a REGULAR
#                     language -- Zeckendorf is "no 11", which is why the class
#                     sizes are Fibonacci in the first place -- read here as a
#                     right-linear grammar over MSB-end BLOCKS, and accepted
#                     only if it reproduces every observed class exactly.  The
#                     class SIZES are `numsys.py`'s fingerprint, used as the
#                     acceptance test rather than as a label.
#
# Ported from `tools/ladder/nofam.py`, which measured the fifteen
# `no value family` rows (docs/LADDER_NOFAM.md).  `nofam.readings` is NOT
# ported: it is a measurement instrument at ~30 s a row.

FIB = [1, 1]
while len(FIB) < 60:
    FIB.append(FIB[-1] + FIB[-2])


def _solve(eqs, W):
    """Exact rational solve of `eqs` = [(coeffs, rhs)] for W unknowns, adding
    equations greedily and COUNTING the ones that contradict what is already
    fixed.  Greedy rather than least-squares on purpose: a handful of
    mid-flight tapes must not drag the fit, they must be counted."""
    from fractions import Fraction
    rows = []          # (pivot, coeffs as Fractions, rhs)
    bad = 0
    for co, rhs in eqs:
        v = [Fraction(x) for x in co]
        r = Fraction(rhs)
        for pv, pc, pr in rows:
            if v[pv]:
                f = v[pv] / pc[pv]
                v = [x - f * y for x, y in zip(v, pc)]
                r -= f * pr
        piv = next((i for i, x in enumerate(v) if x), None)
        if piv is None:
            if r:
                bad += 1
            continue
        rows.append((piv, v, r))
    if not rows:
        return None, bad
    sol = [None] * W
    for pv, v, r in reversed(rows):
        s, ok = r, True
        for i in range(pv + 1, W):
            if v[i]:
                if sol[i] is None:
                    ok = False
                    break
                s -= v[i] * sol[i]
        if ok:
            sol[pv] = s / v[pv]
    return sol, bad


def fit_weights(ds, step=1, maxW=14, max_violated=0.02):
    """A WEIGHT per digit position, from the machine's own enumeration ORDER
    rather than from an assumed radix.

    Inside a width class the strings appear in the order the counter reaches
    them, so the RANK of a string by first appearance is its value if the
    machine is counting at all -- and that is an observation, not an
    assumption.  Returns the weight tuple, or None."""
    order, seen = defaultdict(list), set()
    for d in ds:
        if d is None or d in seen:
            continue
        seen.add(d)
        order[len(d)].append(d)
    eqs, W = [], 0
    for n, ss in order.items():
        if len(ss) < 3 or n > maxW:
            continue
        W = max(W, n)
        for a, b in zip(ss, ss[1:]):
            eqs.append(([(b[i] if i < n else 0) - (a[i] if i < n else 0)
                         for i in range(maxW)], step))
    if len(eqs) < 8 or not W:
        return None
    sol, bad = _solve([(c[:W], r) for c, r in eqs], W)
    if sol is None or bad > max_violated * len(eqs):
        return None
    # Keep the longest DETERMINED prefix.  A position that only ever appears
    # in the widest, half-observed class is not pinned by the equations, and
    # dropping the whole fit for it would throw away a numeration the machine
    # states perfectly at every width below.  Strings wider than the prefix
    # are then simply not read (`Fam.value` returns None there).
    w = []
    for x in sol:
        if x is None or x.denominator != 1 or x <= 0:
            break
        if w and int(x) < w[-1]:
            break                         # weights must not decrease
        w.append(int(x))
    return tuple(w) if len(w) >= 3 else None


def name_weights(w, b):
    if w is None:
        return 'base-%d' % b if b > 1 else 'unary: the value is the run count'
    if all(x == b ** i for i, x in enumerate(w)):
        return 'base-%d' % b
    if all(x == FIB[i] for i, x in enumerate(w)):
        return 'fibonacci'
    if all(x == FIB[i + 1] for i, x in enumerate(w)):
        return 'fibonacci(shifted)'
    return 'weights ' + ','.join(map(str, w[:8]))


def gen_class(classes, k):
    """The width-k canonical strings the grammar generates."""
    blocks, base = classes
    out = {0: frozenset([()])}
    out.update(base)
    for n in range(1, k + 1):
        if n in out:
            continue
        s = set()
        for u in blocks:
            if len(u) <= n:
                s |= {t + u for t in out[n - len(u)]}
        out[n] = frozenset(s)
    return out[k]


def fit_classes(obs, maxu=2, max_blocks=3):
    """The canonical form as a right-linear grammar: C(k) = U_u C(k-|u|) . u
    over a small set of MSB-end BLOCKS, with the low widths taken verbatim.

    `obs` is {width: iterable of digit tuples, LSB-first}.  The grammar must
    reproduce every observed class EXACTLY except at the widest two widths,
    where the walk routinely stops mid-class and containment is all that can
    be asked.  Returns (blocks, base) or None.

    Measured on the dev fixture (`1RB---_0LB1RC_1LB0RD_1LC0RD` at B1/R,
    terminator `11`): blocks `{0, 11}`, class sizes 2, 3, 5, 8, 13, 21, 34 --
    the Fibonacci fingerprint `numsys.py` reports without decoding anything,
    reached here from the strings themselves."""
    ks = sorted(k for k in obs if k > 0)
    if len(ks) < 4 or ks != list(range(1, ks[-1] + 1)):
        return None
    have = {k: frozenset(obs[k]) for k in ks}
    if any(not have[k] for k in ks):
        return None
    top, alpha = ks[-1], sorted({d for k in ks for s in have[k] for d in s})
    cands = [tuple(u) for n in range(1, maxu + 1)
             for u in itertools.product(alpha, repeat=n)]
    for size in range(1, max_blocks + 1):
        for bl in itertools.combinations(cands, size):
            blocks = frozenset(bl)
            base, ok = {0: frozenset([()])}, True
            for k in ks:
                g = gen_class((blocks, base), k)
                if g == have[k]:
                    continue
                if k <= maxu:
                    base[k] = have[k]          # a genuine base case
                    continue
                if k >= top - 1 and have[k] <= g:
                    continue                   # widest widths: half-walked
                ok = False
                break
            if ok:
                return (blocks, base)
    return None


# ------------------------------------------------------------------- family

class Fam:
    """CTR(alph, v): counter segment on `side`, digits nearest-first with the
    LEAST significant digit adjacent to the head."""

    def __init__(self, q, h, side, other, digs, pre, named_by, tail=()):
        self.q, self.h, self.side = q, h, side
        self.other = tuple(other)
        self.digs = [tuple(d) for d in digs]
        self.pre = tuple(pre)
        self.tail = tuple(tail)     # the terminator the discovery read
        # PHASES.  A machine may run the same digit alphabet through several
        # terminators in turn -- lap in phase 0, lap in phase 1, then widen --
        # and a reader pinned to one of them calls the other laps undecodable
        # and reports a fill costing Theta(2^p) (`fillcost.py`).  The phase is
        # part of the family's state, like the width; `tails[0]` is the tail
        # the discovery read, so a one-phase family is exactly today's.
        self.tails = (self.tail,)
        self.named_by = named_by          # digit word -> ladder rule name
        self.l = len(self.digs[0])
        self.b = len(self.digs)
        self.idx = {d: i for i, d in enumerate(self.digs)}
        self.fills = None            # one width law per phase, inferred later
        self.code = 'binary'         # or 'gray': the reflected code
        # How much the value advances per ANCHOR VISIT.  A machine whose
        # lowest cell is a phase bit crosses the anchor once per TWO counter
        # steps, so its chain is +2 and a +1 test rejects it.
        self.step = 1
        # The far side as a run TEMPLATE with a symbolic count: a list of
        # (word, a, b) spelling word^(a*p + b).  None means the one-parameter
        # family -- the far side is the constant cell tuple `other`, which is
        # where the one-parameter assumption used to be baked in.
        self.otmpl = None
        # The near-head PREFIX, likewise: `u^(a*p + b)` instead of a fixed
        # word.  None is today's fixed `pre` and every path below is unchanged.
        self.ptmpl = None
        self.p0 = 0
        self.prange = (0, 0)
        self.templated = False        # found by the far-side TEMPLATE pass
        # THE NUMERATION.  `decode` sums d_i * b**i.  That is one number system
        # out of many, and a machine counting in another reads as `no +1 chain`
        # against the assumption rather than against its own behaviour -- the
        # same error the carry, the anchor, the base, the terminator and the
        # code each were until they became parameters.  `weights` replaces
        # `b**i` by an inferred non-decreasing positive sequence, so the value
        # is Sum d_i * w_i; base-b is w_i = b**i and stays exactly what it is
        # today, which is why None means "positional" and nothing below it
        # changes.  Fibonacci is w = 1, 1, 2, 3, 5, 8.
        self.weights = None
        # The CANONICAL FORM, and it is the real cost of a weight sequence.
        # For b**i the encoder is division.  For a general weight sequence the
        # representation is NOT unique (Fibonacci: 1100 and 0100 are both 2)
        # and the machine uses exactly one of them, so `of_value` has to
        # produce the MACHINE's string and not any string with the right
        # value.  `classes` is the right-linear grammar `fit_classes` reads off
        # the observed width classes -- a regular language, which is why the
        # class sizes are Fibonacci in the first place -- as
        # (blocks, {width: frozenset of base strings}).
        self.classes = None
        self._cls = {}                # width -> [(value, ds)] in value order
        self._byv = {}                # width -> {value: ds}

    def key(self):
        return (self.q, self.h, self.side, self.other, tuple(self.digs),
                self.pre, self.tail, self.code, self.step, self.weights,
                self.ptmpl)

    # ------------------------------------------------------- the far side
    def far_cells(self, p=None):
        """Cells of the far side at outer parameter p."""
        if self.otmpl is None:
            return self.other
        p = self.p0 if p is None else p
        out = []
        for w, a, b in self.otmpl:
            n = a * p + b
            if n < 0:
                return None
            out.extend(list(w) * n)
        while out and out[-1] == 0:
            out.pop()
        return tuple(out)

    def far_p(self, cfg):
        """The p this config's far side spells, or None.

        Deliberately matched on CELLS, not on the run words: replay
        renormalizes a side and can hand back a different block phase for the
        same cell string, so a word-level match would make the anchor test
        depend on how the far side happened to be blocked."""
        oc = runs_cells(self.other_side(cfg))
        if oc is None:
            return None
        oc = tuple(oc)
        if self.otmpl is None:
            return self.p0 if oc == self.other else None
        lo, hi = self.prange
        for p in range(max(0, lo - 2), hi + 4):
            if self.far_cells(p) == oc:
                return p
        return None

    def psample(self, n=3):
        """The p values the arms are mined and checked at.  One is a shape;
        several are a rule -- generalizing across them is what puts p in the
        arm symbolically rather than pinning it."""
        if self.otmpl is None:
            return [self.p0]
        lo, hi = self.prange
        return sorted({min(max(lo, self.p0 + i), hi) for i in range(n)}) or \
            [self.p0]

    @property
    def fill(self):
        """The phase-0 law, for the one-phase reporting paths."""
        return None if not self.fills else self.fills[0]

    def pre_cells(self, p=None):
        """The near-head prefix at outer parameter p.

        4j's sixth defect: `Fam.read` matches the prefix as a FIXED tuple, so a
        machine whose near-head spacer GROWS with the lap -- `0^(2k+5)` on
        `0RB0RD_1LC1RB_1RA0LC_1LB0LC`, read off the tape by John -- returns
        None for every candidate at every anchor, so `n_families = 0`, so the
        row is filed under *no anchor whose counter side decodes*.  The shape
        the prefix wants is the one the FAR side already has (`fit_far`) and
        the one the kernel field already has (`fm_pre` beside the engine's own
        `sside`): a fixed head plus a repeated block whose count is affine in
        p.  `ptmpl` is None on every family the passes above build, and then
        every path here is bit-for-bit what it was."""
        if self.ptmpl is None:
            return self.pre
        p = self.p0 if p is None else p
        out = []
        for w, a, b in self.ptmpl:
            n = a * p + b
            if n < 0:
                return None
            out.extend(list(w) * n)
        return tuple(out)

    def decode(self, cells, ph=0, p=None):
        """cells (nearest-first, trailing blanks stripped) -> digits LSB-first,
        read in PHASE ph at outer parameter p.  Blanks stripped off the far end
        are restored by the pad loop."""
        tail = self.tails[ph]
        pre = self.pre_cells(p)
        if pre is None:
            return None
        base = list(cells)
        if tuple(base[:len(pre)]) != pre:
            return None
        for pad in range(self.l + len(tail) + 1):
            c = base + [0] * pad
            n = len(c) - len(pre) - len(tail)
            if n < 0 or n % self.l:
                continue
            if tail and tuple(c[len(c) - len(tail):]) != tail:
                continue
            mid = c[len(pre):len(pre) + n]
            ds, ok = [], True
            for i in range(0, n, self.l):
                g = tuple(mid[i:i + self.l])
                if g not in self.idx:
                    ok = False
                    break
                ds.append(self.idx[g])
            if ok and self.encode(ds, ph, p) == list(cells):
                return ds
        return None

    def read(self, cells, p=None):
        """(phase, digits) for the first phase that reads these cells."""
        for ph in range(len(self.tails)):
            ds = self.decode(cells, ph, p)
            if ds is not None:
                return ph, ds
        return None, None

    def encode(self, ds, ph=0, p=None):
        cells = list(self.pre_cells(p) or ())
        for d in ds:
            cells.extend(self.digs[d])
        cells.extend(self.tails[ph])
        while cells and cells[-1] == 0:
            cells.pop()
        return cells

    # -------------------------------------------------- the width classes
    def klass(self, k):
        """The width-k members in VALUE order, as [(value, ds)].

        Positional: every digit string of width k, which is what enumerating
        `range(b**k)` has always meant.  With a weight sequence the members are
        the CANONICAL strings only -- the ones the machine actually writes --
        generated from `classes`, so `all_strings` and `reach` cannot report an
        uncovered member the machine never reaches."""
        got = self._cls.get(k)
        if got is not None:
            return got
        if self.weights is None:
            got = [(v, self.of_value(v, k)) for v in range(self.b ** k)]
        elif k > len(self.weights) or self.classes is None:
            got = []
        else:
            got = sorted((self.value(list(ds)), list(ds))
                         for ds in gen_class(self.classes, k))
            self._byv[k] = {v: ds for v, ds in got}
        self._cls[k] = got
        return got

    def maxval(self, k):
        """The top of an octave, on the VALUE.  For b**i that is b**k - 1;
        for a weight sequence it is the largest value the width can spell,
        which is what `is_top` has to compare against."""
        if self.weights is None:
            return self.b ** k - 1
        cl = self.klass(k)
        return cl[-1][0] if cl else -1

    def value(self, ds):
        """Digit string -> the number it denotes, in this family's NUMERATION
        and CODE.  None when the width is past the weights that were fitted --
        a position no equation pinned is not a reading, and the callers stop
        there rather than guessing it."""
        if self.weights is not None:
            if len(ds) > len(self.weights):
                return None
            return sum(d * self.weights[i] for i, d in enumerate(ds))
        ds = gray_decode(ds, self.b) if self.code == 'gray' else ds
        v = 0
        for d in reversed(ds):
            v = v * self.b + d
        return v

    def of_value(self, v, k):
        """The width-k digit string denoting v, in this family's code."""
        if self.weights is not None:
            if k not in self._byv:
                self.klass(k)
            got = self._byv[k].get(v)
            return None if got is None else list(got)
        ns, x = [], v
        for _ in range(k):
            ns.append(x % self.b)
            x //= self.b
        if x:
            return None
        return gray_encode(ns, self.b) if self.code == 'gray' else ns

    def top(self, k):
        """The width-k string the fill leaves from.  For `binary` with step 1
        that is the all-max string, which is what the fill law used to test for
        directly; for a reflected code it is not the all-max string at all, and
        for a weight sequence it is the last member of the width class."""
        if self.weights is not None:
            cl = self.klass(k)
            return list(cl[-1][1]) if cl else None
        return self.of_value(self.b ** k - 1, k)

    def is_top(self, ds):
        """Would the next step overflow this width?  Phrased on the value so
        it is right for any code, any step and any numeration."""
        v = self.value(ds)
        return v is None or v + self.step > self.maxval(len(ds))

    def cfg(self, ds, p=None, ph=0):
        """The counter segment in ITS OWN alphabet -- one run per maximal
        stretch of equal digits -- NOT in the miner's greedy block RLE.  This
        is the whole point of CTR being a tape item: under greedy blocking the
        run words near the head depend on digits arbitrarily far away (a
        period-3 bit pattern invents a 6-cell block word), so no bounded set of
        local shapes covers the family.  Digit-aligned, the run vocabulary is
        the alphabet itself and the near-head runs are a function of the
        near-head digits -- which is what makes the arms LOCAL."""
        pc = self.pre_cells(p)
        if pc is None:
            return None
        # A digit the alphabet does not have is not a configuration.  The fill
        # law can produce one -- the default is the odometer carry, whose
        # target suffix is the digit `1`, and a UNARY family has only the digit
        # `0` -- and the caller's contract for that has always been None.
        if any(d < 0 or d >= self.b for d in ds):
            return None
        runs = [((c,), Expr(1)) for c in pc]
        i = 0
        while i < len(ds):
            k = i
            while k < len(ds) and ds[k] == ds[i]:
                k += 1
            runs.append(canon_run(self.digs[ds[i]], Expr(k - i)))
            i = k
        runs.extend(((c,), Expr(1)) for c in self.tails[ph])
        out = []
        for w, e in runs:
            if out and out[-1][0] == w:
                out[-1] = (w, out[-1][1] + e)
            else:
                out.append((w, e))
        while out and set(out[-1][0]) == {0}:
            out.pop()
        c = tuple(out)
        fc = self.far_cells(p)
        if fc is None:
            return None
        o = block_rle(list(fc))
        return (self.q, self.h, c, o) if self.side == 'L' else \
               (self.q, self.h, o, c)

    def counter_side(self, cfg):
        return cfg[2] if self.side == 'L' else cfg[3]

    def other_side(self, cfg):
        return cfg[3] if self.side == 'L' else cfg[2]

    def anchor_shaped(self, cfg):
        if (cfg[0], cfg[1]) != (self.q, self.h):
            return False
        return self.far_p(cfg) is not None

    def visible(self, cfg, env=None):
        """Counter-side cells up to the wall marker; (cells, marker_seen)."""
        out = []
        for w, e in self.counter_side(cfg):
            if w == MARKER:
                return out, True
            n = e.subst(env or {})
            if not n.is_const() or n.c < 0:
                return None, None
            out.extend(list(w) * n.c)
        while out and out[-1] == 0:
            out.pop()
        return out, False

    def aligned(self, cells, p=None):
        """Is this a digit-aligned PREFIX of some family member?  The wall
        marker hides the rest, so a local arm's landing config can only be
        checked this far -- but this far is enough to catch a stop that is
        mid-digit, which is what landing off the family looks like."""
        pre = self.pre_cells(p)
        if pre is None:
            return False
        n = min(len(cells), len(pre))
        if tuple(cells[:n]) != pre[:n]:
            return False
        mid = cells[len(pre):]
        full, rem = divmod(len(mid), self.l)
        for i in range(full):
            if tuple(mid[i * self.l:(i + 1) * self.l]) not in self.idx:
                return False
        if rem:
            part = tuple(mid[full * self.l:])
            if not any(d[:rem] == part for d in self.digs):
                return False
        return True

    def member(self, cfg, env=None):
        """Anchor-shaped AND actually a family MEMBER -- the counter side
        decodes to a digit string (or, behind the wall, is digit-aligned so
        far).

        `anchor_shaped` alone is not enough to stop an arm's replay at: the
        head crosses the anchor cell several times per increment and the far
        side is often back in place mid-carry, so the FIRST anchor-shaped
        config an arm reaches is routinely a mid-flight tape that decodes to
        nothing.  Stopping there is what "arm lands off the family" is, and it
        is the same class of bug as the differential probe fixed in cf7eeab --
        both stopped at an anchor VISIT instead of at a family MEMBER."""
        if not self.anchor_shaped(cfg):
            return False
        cells, mk = self.visible(cfg, env)
        if cells is None:
            return False
        pp = self.far_p(cfg)
        return self.aligned(cells, pp) if mk \
            else self.read(cells, pp)[1] is not None

    def view(self, cfg, m, marker=True):
        """Local view: the counter side is truncated at m runs behind a wall
        marker; the other side stays exact.  With marker=True the wall is
        appended even when the side is SHORTER than the window -- the rule is
        then a generalization of this config to any rest, which is what makes
        one arm cover a whole carry class.  marker=False keeps the side exact,
        which is what the overflow arm needs (it must see the end)."""
        cs = self.counter_side(cfg)
        if marker:
            cs = cs[:m] + ((MARKER, Expr(1)),)
        os = self.other_side(cfg)
        return (cfg[0], cfg[1], cs, os) if self.side == 'L' else \
               (cfg[0], cfg[1], os, cs)

    def json(self):
        return {'state': chr(65 + self.q), 'head': self.h, 'side': self.side,
                'other_side_cells': list(self.other),
                'digits': [list(d) for d in self.digs],
                'digit_named_by': {''.join(map(str, w)): r
                                   for w, r in self.named_by.items()},
                'alphabet_provenance': (
                    'digit word named by a ladder rule'
                    if self.named_by else
                    'digit width from a ladder rule word; values pinned by '
                    'the +1 chain'),
                'near_head_prefix': list(self.pre),
                'near_head_prefix_template': (
                    None if self.ptmpl is None else
                    ['%s^(%d*p+%d)' % (''.join(map(str, w)), a, b)
                     for w, a, b in self.ptmpl]),
                'terminator': list(self.tail),
                'terminators_by_phase': [list(t) for t in self.tails],
                'n_phases': len(self.tails),
                'base': self.b, 'digit_len': self.l,
                'code': self.code,
                'value_step_per_anchor_visit': self.step,
                'numeration': name_weights(self.weights, self.b),
                'weights': (None if self.weights is None
                            else list(self.weights)),
                'canonical_form': (None if self.classes is None else {
                    'blocks': [list(u) for u in sorted(self.classes[0])],
                    'base_widths': sorted(self.classes[1]),
                    'class_sizes': [len(self.klass(k))
                                    for k in range(1, min(
                                        9, len(self.weights or ()) + 1))]}),
                'order': 'LSB nearest head'}


class Fill:
    """The FILL LAW: what the top string of width p goes to.

    `next_ds` used to hard-code the odometer carry -- all-max of width p goes
    to `[0]*p ++ [1]`, the value b^p -- and then reported every machine that
    does something else as "overflow leaves the family".  The law is a
    property of the machine, so it is read off the trace like the alphabet and
    the digit values are: observe the top string's successor at two widths and
    interpolate.

    The interpolant is `pre ++ mid^n ++ suf` at width `p + s`, which is the
    smallest shape closing over what the rows actually do: the carry
    (`s=1, suf=[1]`), the reset-and-widen (`s=1`, nothing else), the
    parity-two widen (`s=2`) -- and, with a non-empty `pre`/`suf`, the fills
    that land on a fixed low string at the new width.  One `find_IH` at the
    width level; the arms below it are unchanged.

    `to` is the PHASE the fill lands in.  A one-phase family fills back into
    itself and `to` is 0, which is what every closed row does today; a
    multi-phase counter laps once per terminator, so its phase-0 fill lands in
    phase 1 without widening at all and only the last phase's fill moves p."""

    __slots__ = ('s', 'pre', 'mid', 'suf', 'seen', 'pa', 'pb', 'pc', 'to')

    def __init__(self, s, pre=(), mid=0, suf=(), seen=(), pa=1, pb=0, pc=0,
                 to=0):
        self.s, self.mid, self.to = s, mid, to
        self.pre, self.suf = tuple(pre), tuple(suf)
        self.seen = tuple(seen)
        # the OUTER parameter's law across the fill: p' = pa*p + pb*k + pc.
        # Identity (1, 0, 0) is the one-parameter family, where the fill does
        # not touch the far side at all.
        self.pa, self.pb, self.pc = pa, pb, pc

    def apply_p(self, p, k):
        return self.pa * p + self.pb * k + self.pc

    def moves_p(self):
        return (self.pa, self.pb, self.pc) != (1, 0, 0)

    def apply(self, k):
        n = k + self.s - len(self.pre) - len(self.suf)
        if n < 0:
            return None
        return list(self.pre) + [self.mid] * n + list(self.suf)

    def is_carry(self):
        return (self.s, self.pre, self.mid, self.suf, self.to) == \
            (1, (), 0, (1,), 0)

    def json(self):
        return {'widens_by': self.s, 'target_prefix': list(self.pre),
                'target_fill_digit': self.mid, 'target_suffix': list(self.suf),
                'law': 'E(p, b^p - 1) -> E(p+%d, %s)'
                       % (self.s, ''.join(map(str, self.pre)) + '<%d>' % self.mid
                          + ''.join(map(str, self.suf))),
                'inferred_from_widths': list(self.seen),
                'lands_in_phase': self.to,
                'outer_p_law': "p' = %d*p + %d*k + %d" % (self.pa, self.pb,
                                                          self.pc),
                'fill_moves_outer_p': self.moves_p(),
                'is_the_odometer_carry': self.is_carry()}


CARRY = Fill(1, (), 0, (1,))

# The codes and steps the family search will read a counter segment in.
# Positional and one-step first, always: a row that already reads as a plain
# odometer advancing once per visit must keep reading that way.
CODES = ('binary', 'gray')
STEPS = (1, 2)

# The stand-in a visit's near-head prefix carries when the prefix is a
# TEMPLATE rather than a fixed word.  `_try_parse` breaks a chain whenever two
# consecutive visits spell different prefix cells; a prefix that grows with the
# lap spells different cells at every visit BY CONSTRUCTION, so the identity
# the chain must test is "the prefix the template predicts at this visit's p",
# which is true of every visit that parsed at all.
PTMPL = ('the prefix template',)


def fit_fill(obs):
    """[(k, target digit string)] -> Fill, or None.

    Two observations at different widths pin (s, pre, mid, suf); the rest are
    a check.  Interpolation, not a guess: a law that does not reproduce every
    observed fill is rejected outright."""
    obs = [(k, list(t)) for k, t in obs if t is not None]
    if len(obs) < 2:
        return None
    ss = {len(t) - k for k, t in obs}
    if len(ss) != 1:
        return None
    s = ss.pop()
    a, b = sorted(obs, key=lambda x: x[0])[:2]
    if a[0] == b[0]:
        return None
    ta, tb = a[1], b[1]
    p = 0
    while p < min(len(ta), len(tb)) and ta[p] == tb[p]:
        p += 1
    q = 0
    while (q < min(len(ta), len(tb)) - p and ta[-1 - q] == tb[-1 - q]):
        q += 1
    mids = {d for t in (ta, tb) for d in t[p:len(t) - q]}
    if len(mids) > 1:
        return None
    mid = mids.pop() if mids else 0
    pre, suf = ta[:p], ta[len(ta) - q:] if q else []
    while pre and pre[-1] == mid:
        pre.pop()
    while suf and suf[0] == mid:
        suf.pop(0)
    f = Fill(s, pre, mid, suf, sorted(k for k, _ in obs))
    return f if all(f.apply(k) == t for k, t in obs) else None


WIDEN = Fill(1, (), 0, ())


def fam_fill(fam, ph):
    """Phase ph's fill law, defaulting to the odometer carry -- except for a
    UNARY family, whose only possible fill is the pure widening: the carry's
    target suffix is the digit `1` and a one-digit alphabet has no such digit,
    so the default has to be `word^p -> word^(p+1)`."""
    dflt = WIDEN if fam.b == 1 else CARRY
    if not fam.fills:
        return dflt
    f = fam.fills[ph] if ph < len(fam.fills) else None
    return f or dflt


def next_ds(fam, ds, ph=0):
    """Successor inside a width; the phase's FILL LAW at the top.

    Stated on the VALUE rather than as a digit-wise carry ripple, so it is
    right for any code the family reads in, any numeration it counts in and any
    step it advances by.  For `binary` with step 1 this is exactly the odometer
    carry; for a UNARY family every string is the top, so the successor is
    always the fill and the interior/overflow split collapses to one arm."""
    v = fam.value(ds)
    if v is None:
        return None
    if v + fam.step > fam.maxval(len(ds)):
        return fam_fill(fam, ph).apply(len(ds))
    return fam.of_value(v + fam.step, len(ds))


def succ(fam, ds, p, ph=0):
    """The family's successor on (digit string, outer parameter, PHASE).

    The interior arms never touch p or the phase -- that is the whole
    discipline: they carry over unchanged from the one-parameter family.  The
    FILL is the only arm that crosses either, and which phase it lands in is
    read off the machine like everything else (`fit_fills`)."""
    nd = next_ds(fam, ds, ph)
    if nd is None:
        return None, None, None
    if len(nd) == len(ds) and not fam.is_top(ds):
        return nd, p, ph
    f = fam_fill(fam, ph)
    return nd, f.apply_p(p, len(ds)), f.to


def fit_fill_p(obs):
    """[(p, k, p')] -> (pa, pb, pc) with p' = pa*p + pb*k + pc, or None.

    Exact fit only, and identity is preferred when it explains the data, so a
    family whose far side simply does not move keeps the one-parameter law."""
    obs = [(p, k, r) for p, k, r in obs if None not in (p, k, r)]
    if not obs:
        return (1, 0, 0)
    if all(r == p for p, k, r in obs):
        return (1, 0, 0)
    for pa in (1, 0, 2):
        for pb in (0, 1, 2, -1):
            cs = {r - pa * p - pb * k for p, k, r in obs}
            if len(cs) == 1:
                return (pa, pb, cs.pop())
    return None


_WALKS = {}


def raw_anchor_visits(tm, q, h, steps=150000, cap=6000):
    """Every visit to the anchor CELL of the raw run, as (left runs, right
    runs).  Cached per (state, head): a row tries up to six candidate families
    and several of them share an anchor, and this walk is the single most
    expensive thing `close` does outside the arm search."""
    key = (q, h, steps, cap)
    got = _WALKS.get(key)
    if got is not None:
        return got
    tape, pos, cq, lo, hi = {}, 0, 0, 0, 0
    out = []
    for _ in range(steps):
        cell = tape.get(pos, 0)
        if cq == q and cell == h and len(out) < cap:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            out.append((block_rle(gl), block_rle(gr)))
        tr = tm.get((cq, cell))
        if tr is None:
            break
        w, d, cq = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
    _WALKS[key] = out
    return out


def anchor_cells(fam, tm, steps=150000, cap=6000):
    """(counter-side cells, p) at every anchor visit, from the RAW machine.

    Its own run rather than the miner's snapshots, because the fill law needs
    to see several OCTAVES and the mining trace is only long enough for one or
    two -- a counter that widens by two reaches its second fill somewhere past
    where the ladder stopped looking.  Only anchor visits materialize a side,
    so the extra length is nearly free.  Cells, not digits: the PHASE pass
    has to ask what a visit would read as under another terminator, and that
    question is not answerable once the reading has already been made."""
    out = []
    for L, R in raw_anchor_visits(tm, fam.q, fam.h, steps, cap):
        cfg = (fam.q, fam.h, L, R)
        pp = fam.far_p(cfg)
        if pp is None:
            continue
        c = runs_cells(fam.counter_side(cfg))
        out.append((None if c is None else tuple(c), pp))
    return out


def anchor_seq(fam, tm, steps=150000, cap=6000):
    """(digits, p) at every anchor visit -- phase 0 only, for the probes that
    predate phases."""
    return [(None if c is None else fam.decode(list(c), 0, pp), pp)
            for c, pp in anchor_cells(fam, tm, steps, cap)]


def read_seq(fam, walk):
    """[(phase, digits, p)] over an `anchor_cells` walk; (None, None, p) for a
    visit no phase reads."""
    out = []
    for c, pp in walk:
        if c is None:
            out.append((None, None, pp))
            continue
        ph, ds = fam.read(list(c), pp)
        out.append((ph, ds, pp))
    return out


def chain_frac(fam, seq):
    """Fraction of consecutive READ visits that the model's own successor
    explains -- either the next member is `succ` of this one, or it is this one
    again (the head crosses the anchor cell twice without the counter moving).

    This is the guard on the phase pass: an extra terminator that reads a lot
    of mid-flight tapes would raise the read fraction and destroy the chain, so
    the chain is what decides, not the count."""
    got = [(ph, ds, pp) for ph, ds, pp in seq if ds]
    if len(got) < 4:
        return 0.0
    ok = 0
    for (ph, ds, pp), (ph2, ds2, pp2) in zip(got, got[1:]):
        if (ph, ds, pp) == (ph2, ds2, pp2):
            ok += 1
            continue
        nd, npp, nph = succ(fam, ds, pp, ph)
        if nd is not None and (nph, nd, npp) == (ph2, ds2, pp2):
            ok += 1
    return ok / (len(got) - 1)


def observe_fill(fam, walk, want=12):
    """Read the fill law off the anchor visits: every time the machine sits on
    the top string of some width IN SOME PHASE, record the phase, the width,
    the outer parameter, and where the next family MEMBER is -- phase, string
    and outer parameter.

    The member, not the next visit.  The fill widens the counter, and the head
    crosses the anchor cell several times on the way, so the successor of a top
    string is several anchor visits along and every visit in between decodes to
    nothing.  It used to scan a fixed 16 visits ahead; measured on the 41
    `overflow leaves the family` rows the gap GROWS with the width (7, 25, 97,
    385, 1537 visits on 1RB1LA_1LC0RD_1LA1LB_0LB1RD), so a constant window sees
    at most one width and `fit_fill` needs two -- 21 of those 41 fell back to
    the hard-coded carry for want of a second observation.  The scan now runs
    to the next member however far that is."""
    seq = read_seq(fam, walk)
    obs, seen = [], set()
    for i, (ph, a, pa) in enumerate(seq):
        if not a or not fam.is_top(a):
            continue
        if (ph, len(a), pa) in seen:
            continue
        for j in range(i + 1, len(seq)):
            ph2, b, pb = seq[j]
            if b is None or (ph2, b, pb) == (ph, a, pa):
                continue
            seen.add((ph, len(a), pa))
            obs.append((ph, len(a), ph2, b, pa, pb))
            break
        if len(obs) >= want:
            break
    return obs


def fit_fills(fam, obs):
    """One `Fill` per phase, or None if some phase's law does not interpolate.

    Per phase because the phases do different things: on the measured rows the
    early phases hand over at the same width and only the last one widens."""
    out = []
    for ph in range(len(fam.tails)):
        mine = [o for o in obs if o[0] == ph]
        tos = {o[2] for o in mine}
        if len(tos) > 1:
            return None            # the fill's target phase is not a function
        f = fit_fill([(k, t) for _, k, _, t, _, _ in mine])
        if f is None:
            if len(fam.tails) > 1:
                return None        # a phase with no law is not a reading
            d = WIDEN if fam.b == 1 else CARRY
            f = Fill(d.s, d.pre, d.mid, d.suf)
        f.to = tos.pop() if tos else 0
        plaw = fit_fill_p([(pa, k, pb) for _, k, _, _, pa, pb in mine])
        if plaw is None:
            plaw = (1, 0, 0)
        f.pa, f.pb, f.pc = plaw
        out.append(f)
    return out


def fit_phases(fam, walk, max_phases=4, min_visits=8, min_chain=0.95):
    """Terminators beyond the one the discovery read, inferred like everything
    else: take the anchor visits no phase reads yet and ask which single
    terminator reads the most of them, keeping the anchor, the digits, the base
    and the far side exactly as the family read them.

    Guarded three ways, and the guards are what keep a row that closes today
    closed.  A candidate phase must read at least `min_visits` distinct visits;
    every phase must then have a fill law that interpolates (`fit_fills`), with
    a single target phase; and the whole reading must be a CHAIN -- the model's
    own successor has to explain at least `min_chain` of the consecutive read
    visits.  A terminator that merely reads a lot of mid-flight tapes raises
    the read count and destroys the chain, so it is the chain that decides.
    When nothing qualifies the family is left exactly as it was."""
    cells = [(c, pp) for c, pp in walk if c is not None]
    if not cells:
        return False

    def fit(tails):
        fam.tails = tuple(tails)
        fam.fills = None
        fills = fit_fills(fam, observe_fill(fam, walk, want=6 * len(tails)))
        if fills is None:
            return None
        fam.fills = fills
        seq = read_seq(fam, walk)
        return sum(1 for _, ds, _ in seq if ds), chain_frac(fam, seq)

    base = list(fam.tails)
    got0 = fit(base)
    tails = list(base)
    uniq = list(dict.fromkeys(cells))
    while len(tails) < max_phases:
        fam.tails = tuple(tails)
        unread = [(c, pp) for c, pp in uniq
                  if all(fam.decode(list(c), i, pp) is None
                         for i in range(len(tails)))]
        if not unread:
            break
        cand = set()
        for c, _ in unread:
            for tl in range(2 * fam.l + 2):
                cand.add(tuple(c[len(c) - tl:]) if tl else ())
        # every candidate is scored by what it READS, not by how often its
        # cells happen to appear: a frequent suffix that reads a shifted digit
        # is exactly the misreading this pass exists to avoid
        pick, best_n = None, min_visits - 1
        for t in sorted(cand, key=lambda t: (-len(t), t)):
            if t in tails:
                continue
            fam.tails = tuple(tails + [t])
            n = sum(1 for c, pp in unread
                    if fam.decode(list(c), len(tails), pp) is not None)
            if n > best_n:
                pick, best_n = t, n
        if pick is None:
            break
        tails.append(pick)
    if len(tails) == len(base):
        fit(base)
        return False
    # longest reading first, then shorter ones: the greedy can overshoot with a
    # phase that reads visits no fill law explains
    for n in range(len(tails), len(base), -1):
        got = fit(tails[:n])
        if got is None:
            continue
        read, chain = got
        if chain >= min_chain and (got0 is None or read > got0[0]):
            return True
    fit(base)
    return False


def fit_far(fam, occ):
    """Generalize the far side from a CONSTANT cell tuple to a run TEMPLATE
    with a symbolic count p.

    The one-parameter assumption lives in `Fam.other`: the family is pinned to
    one far-side cell string, so every anchor visit whose far side has moved
    is invisible to it, and a fill that moves the far side leaves the family
    by construction.  Grouping the visits by the far side's run WORDS instead
    of its cells puts them all back in one group, and inside that group the
    counts are fitted: one coordinate carries p, the rest are affine in it.
    A family whose far side does not move fits the identity and keeps exactly
    its one-parameter behaviour."""
    ref = block_rle(list(fam.other))
    words = tuple(w for w, _ in ref)
    rows = []
    for _, sn in occ:
        if (sn[0], sn[1]) != (fam.q, fam.h):
            continue
        far = fam.other_side(sn)
        if tuple(w for w, _ in far) != words:
            continue
        cs = [e.c for _, e in far if e.is_const()]
        if len(cs) == len(far):
            rows.append(tuple(cs))
    if len(rows) < 4 or not words:
        return False
    cols = list(zip(*rows))
    mov = [i for i, c in enumerate(cols) if len(set(c)) > 1]
    if not mov:
        return False
    car = mov[0]
    tmpl = []
    for i, w in enumerate(words):
        if i == car:
            tmpl.append((w, 1, 0))
            continue
        pts = {(r[car], r[i]) for r in rows}
        xs = sorted({x for x, _ in pts})
        if len({y for _, y in pts}) == 1:
            tmpl.append((w, 0, next(iter({y for _, y in pts}))))
            continue
        if len(xs) < 2:
            return False
        d = {}
        for x, y in pts:
            if d.setdefault(x, y) != y:
                return False
        a_num, a_den = d[xs[1]] - d[xs[0]], xs[1] - xs[0]
        if a_den == 0 or a_num % a_den:
            return False
        a = a_num // a_den
        b = d[xs[0]] - a * xs[0]
        if any(y != a * x + b for x, y in pts):
            return False
        tmpl.append((w, a, b))
    ps = sorted({r[car] for r in rows})
    fam.otmpl, fam.prange = tuple(tmpl), (ps[0], ps[-1])
    fam.p0 = next((r[car] for r in rows
                   if tuple(fam.far_cells(r[car]) or ()) == fam.other), ps[0])
    # the template has to reproduce every observed far side exactly, or it is
    # not a reading of the machine and the family stays one-parameter
    for r in rows:
        if fam.far_cells(r[car]) is None:
            fam.otmpl = None
            return False
    if fam.far_cells(fam.p0) != fam.other:
        fam.otmpl = None
        return False
    return len(ps) > 1


# ----------------------------------------------------------------- discovery

def find_families(tm, snaps, rules, max_anchor=8, min_chain=8, max_occ=200,
                  max_other=3, numeration=False, weak_chain=12):
    """Anchor + alphabet inference.  Returns [(Fam, first_t, chain_len)].

    The anchors of a counter machine are a SUBSEQUENCE of the visits to their
    (state, head): the head passes the same cell mid-carry too, and the far
    side is usually mid-flight then.  So occurrences are first grouped by the
    far side's contents, and the "+1 per visit" test runs inside a group.
    """
    named = digit_words(rules)
    if not named:
        return []
    seeds = {}
    for w, rn in named.items():
        for r in rots(w):
            seeds.setdefault(r, rn)
    lens = _widths(named)

    byqh = defaultdict(list)
    for t, s in snaps:
        if s is None:
            break
        byqh[(s[0], s[1])].append((t, s))

    found, seen = [], set()
    sides = []
    order = sorted(byqh.items(), key=lambda kv: -len(kv[1]))[:max_anchor]
    for (q, h), occ in order:
        if len(occ) < min_chain:
            continue
        occ = occ[-max_occ:]
        for side in ('L', 'R'):
            cs, os = [], []
            for t, s in occ:
                c = runs_cells(s[2] if side == 'L' else s[3])
                o = runs_cells(s[3] if side == 'L' else s[2])
                cs.append(c)
                os.append(tuple(o) if o is not None else None)
            pop = Counter(o for o in os if o is not None)
            sides.append((q, h, side, byqh[(q, h)], occ, cs, os))
            for other, n in pop.most_common(max_other):
                if n < min_chain:
                    break
                sel = [i for i in range(len(occ)) if os[i] == other]
                suf = _common_suffix([cs[i] for i in sel if cs[i]])
                for l in lens:
                    for tl in range(min(len(suf), 2 * l) + 1):
                        tail = tuple(suf[len(suf) - tl:]) if tl else ()
                        for p in range(l):
                          for code in CODES:
                            for stp in STEPS:
                                fam = _try_parse(q, h, side, other, occ, cs,
                                                 sel, l, p, tail, seeds,
                                                 min_chain, code=code,
                                                 step=stp)
                                if fam is None or fam[0].key() in seen:
                                    continue
                                seen.add(fam[0].key())
                                found.append(fam)
            # The TEMPLATE pass, under the gate 4e gave it.
            if pop and pop.most_common(1)[0][1] >= min_chain:
                continue
            _template_pass(q, h, side, occ, cs, os, seeds, lens, min_chain,
                           found, seen)
    # The second chance, and it runs only when everything above found NOTHING.
    # That gate is deliberate and it is what keeps 4e/4f/4g's closed rows
    # closed: a row that reads as a positional odometer today never reaches
    # any of this, so it cannot be re-read into a worse family and cannot lose
    # a per-candidate time slice to a fallback.  The cost is paid only by the
    # rows that today return `no value family` in seconds with the whole
    # budget left -- which is exactly the fifteen.
    if not found:
        end = time.time() + 40.0
        for q, h, side, full, occ, cs, os in sides[:6]:
            # 1. the far-side TEMPLATE pass, ungated and with 4g's two axes.
            #    LADDER_NOFAM.md's first and second unchanged defects: the
            #    pass is switched off whenever ANY constant-far-side group
            #    reaches the chain threshold, and on
            #    `0RB0RD_1LC1RB_1RA0LC_1LB0LC` the large group is the one that
            #    is NOT the family; and inside it `_try_parse` is called with
            #    neither `code=` nor `step=`, so a two-parameter family could
            #    only ever be binary/+1 while `0RB0RD_1LC1RB_1RA0LC_1LD0LC`
            #    reads at +2.
            _template_pass(q, h, side, occ, cs, os, seeds, lens, min_chain,
                           found, seen, codes=CODES, steps=STEPS, wide=True)
            # 2. the near-head PREFIX as a run template (4j's sixth defect).
            _pre_pass(q, h, side, occ, cs, os, seeds, lens, min_chain,
                      found, seen)
            # 3. the NUMERATION.
            _weights_pass(q, h, side, full, seeds, lens, min_chain,
                          found, seen, deadline=end)
        # 4. and the UNARY counter last of all, only if nothing above read the
        #    row.  Strongest reading first is the same discipline 4e applied to
        #    the far-side template and 4g to the code and the step; the unary
        #    reading is the weakest one there is and it must not be allowed to
        #    crowd out a positional or a weighted one.
        if not found:
            for q, h, side, full, occ, cs, os in sides[:6]:
                _unary_pass(q, h, side, occ, cs, os, seeds, lens, min_chain,
                            found, seen)
    # The NUMERATION pass, run a SECOND way: when the main pass found only
    # families whose anchor chain never gets off the floor (LADDER_PLAN 4s).
    #
    # `if not found` above is an ALL-OR-NOTHING gate, and it is the reason the
    # seven surviving fibonacci rows had never been read as fibonacci: the
    # main pass returns 26 positional families for
    # `1RB---_0LC1RD_1LB1RC_1LB0RD`, every one of them at chain 8 -- which is
    # `min_chain`, the FLOOR -- and 26 > 0 switches the numeration pass off
    # entirely.  The five rows wave 4r boarded found zero positional families,
    # fell through to the numeration pass, and read at chains of 89..290.  The
    # difference between the two halves of that bucket was never the machine;
    # it was whether junk cleared a threshold first.
    #
    # So the gate is restated as a COMPARISON rather than a presence test: if
    # nothing found so far reads more than `weak_chain` consecutive anchor
    # visits, the row has not been read, and the numeration pass runs.  A row
    # that reads plainly today has a long chain (every closed row in the tree
    # is far above this floor) and is untouched, which is the property the
    # `if not found` gate was protecting.  Weighted families then sort by
    # chain like any other, so a genuine positional reading still wins.
    if found and numeration and max(f[2] for f in found) <= weak_chain:
        end = time.time() + 40.0
        for q, h, side, full, occ, cs, os in sides[:6]:
            _weights_pass(q, h, side, full, seeds, lens, min_chain,
                          found, seen, deadline=end)
    # longest chain first; ties to the cleanest reading (shortest terminator,
    # no near-head prefix, narrowest digit).  Template families sort AFTER
    # every constant-far-side one however long their chain, and a non-
    # positional code or a step other than 1 sorts after the plain reading:
    # all three are fallbacks, and a row that reads plainly must keep to it.
    #
    # One tie-break sits between the chain and the shape: a family every one
    # of whose digit words ends in a BLANK, with no terminator behind them,
    # spells one cell more than a [cconf] can carry (LADDER_PLAN 4s).  A
    # `cconf` holds no trailing blanks -- that is what `lpad_eqb` is for -- so
    # the boot's own cells are the family's spelling minus its last cell, and
    # every emitter boot check rejects it with `boot cells ... are not the
    # family at ...`.  It is a property of the DENOTATION and not of the
    # machine: the same anchor rotated one cell reads the same counter with
    # words ending in a 1, and both readings are in `found` at the same chain
    # length.  So this only ever fires on an exact tie in (fallback flags,
    # chain), and when it fires it picks the reading the kernel can state.
    def _blank_tail(f):
        return int(not f.tail and all(d and d[-1] == 0 for d in f.digs))

    found.sort(key=lambda f: (f[0].templated, f[0].code != 'binary',
                              f[0].step != 1, -f[2], _blank_tail(f[0]),
                              len(f[0].tail), len(f[0].pre), f[0].l))
    return found


def _template_pass(q, h, side, occ, cs, os, seeds, lens, min_chain,
                   found, seen, codes=('binary',), steps=(1,), wide=False):
    """The far side as a run TEMPLATE.

    Grouping by the far side's CELLS splits an anchor whose far side moves into
    one small group per p, and when every group falls under min_chain the
    anchor reads as no counter at all -- which is what the `far side varies`
    rows are.  Group by the far side's run WORDS instead and the groups merge;
    the chain then runs +1 inside a p and is allowed to cross p exactly at the
    top string, which is the two-parameter family's own successor.

    `codes`/`steps` are 4g's two axes, which this pass could not use: it called
    `_try_parse` with neither, so a two-parameter family was binary/+1 or
    nothing.  `wide` runs the near-head prefix past the digit width, which
    `p in range(l)` denies a one-cell digit outright."""
    wt = [tuple(w for w, _ in (s2[3] if side == 'L' else s2[2]))
          for _, s2 in occ]
    for words, n in Counter(wt).most_common(2):
        if n < min_chain or not words:
            break
        sel = [i for i in range(len(occ))
               if wt[i] == words and os[i] is not None]
        pids = [os[i] for i in sel]
        if len(sel) < min_chain or len(set(pids)) < 2:
            continue
        other = Counter(pids).most_common(1)[0][0]
        suf = _common_suffix([cs[i] for i in sel if cs[i]])
        for l in lens:
            for tl in range(min(len(suf), 2 * l) + 1):
                tail = tuple(suf[len(suf) - tl:]) if tl else ()
                for p in range(l + 2 if wide else l):
                    for code in codes:
                        for stp in steps:
                            fam = _try_parse(q, h, side, other, occ, cs, sel,
                                             l, p, tail, seeds, min_chain,
                                             code=code, step=stp, pids=pids)
                            if fam is None or fam[0].key() in seen:
                                continue
                            seen.add(fam[0].key())
                            fam[0].templated = True
                            if not fit_far(fam[0], occ):
                                continue      # far side does not fit a*p+b
                            found.append(fam)


def _unary_pass(q, h, side, occ, cs, os, seeds, lens, min_chain, found, seen,
                max_other=3):
    """The counter side as a run template `word^p`, alphabet size 1, `p` the
    run count -- the seventh constructor LADDER_NOFAM.md names, and the mirror
    of `fit_far`, which already fits `word^(a*p + b)` on the far side.

    The same grouping the ordinary pass uses: one constant-far-side group, the
    ladder's own digit widths, the group's common suffix as the terminator.
    Only the alphabet size differs, and with it everything the alphabet size
    decides -- `maxval(k)` is 0, so every string is the top, so there is no
    interior arm, no octave-top test and no fill law to infer."""
    pop = Counter(o for o in os if o is not None)
    for other, n in pop.most_common(max_other):
        if n < min_chain:
            break
        sel = [i for i in range(len(occ)) if os[i] == other]
        suf = _common_suffix([cs[i] for i in sel if cs[i]])
        for l in lens:
            for tl in range(min(len(suf), 2 * l) + 1):
                tail = tuple(suf[len(suf) - tl:]) if tl else ()
                for p in range(l + 2):
                    got = _try_parse(q, h, side, other, occ, cs, sel, l, p,
                                     tail, seeds, min_chain, unary=True)
                    if got is None or got[0].key() in seen:
                        continue
                    seen.add(got[0].key())
                    found.append(got)


def _pre_pass(q, h, side, occ, cs, os, seeds, lens, min_chain, found, seen,
              max_word=3):
    """The near-head PREFIX as a run template `u^(a*p + b)` -- 4j's sixth
    defect, and the sixth time an assumption about the counter's own spelling
    was reported as the machine's failure.

    `Fam.read` matches the prefix as a FIXED tuple.  John's bouncer counter
    spells `0^(2k+5)` there, so `read()` returns None at every candidate at
    every anchor and the row is filed under *no anchor whose counter side
    decodes*.  The p comes from the same place the far side's does -- the
    far-side run template `fit_far` fits -- so the two sides are parameterized
    by ONE quantity, which is what makes it a family and not two clocks."""
    wt = [tuple(w for w, _ in (s2[3] if side == 'L' else s2[2]))
          for _, s2 in occ]
    for words, n in Counter(wt).most_common(2):
        if n < min_chain or not words:
            break
        sel = [i for i in range(len(occ))
               if wt[i] == words and os[i] is not None]
        if len(sel) < min_chain or len({os[i] for i in sel}) < 2:
            continue
        other = Counter(os[i] for i in sel).most_common(1)[0][0]
        prov = Fam(q, h, side, other, [(0,)], (), {})
        if not fit_far(prov, [occ[i] for i in sel]):
            continue
        ps = [prov.far_p(occ[i][1]) for i in sel]
        if len({x for x in ps if x is not None}) < 3:
            continue
        for wl in range(1, max_word + 1):
            c0 = cs[sel[0]]
            if not c0 or len(c0) < wl:
                continue
            u = tuple(c0[:wl])
            if not any(u):
                u = (0,) * wl          # a blank spacer is the commonest case
            cnt, ok = {}, True
            for j, i in enumerate(sel):
                c, pp = cs[i], ps[j]
                if c is None or pp is None:
                    continue
                m = 0
                while tuple(c[m * wl:(m + 1) * wl]) == u:
                    m += 1
                if cnt.setdefault(pp, m) != m:
                    ok = False
                    break
            xs = sorted(cnt)
            if not ok or len(xs) < 3:
                continue
            num, den = cnt[xs[1]] - cnt[xs[0]], xs[1] - xs[0]
            if not num or not den or num % den:
                continue
            a = num // den
            b = cnt[xs[0]] - a * xs[0]
            if any(cnt[x] != a * x + b for x in xs) or a * min(xs) + b < 0:
                continue
            plens = [None if ps[j] is None else wl * (a * ps[j] + b)
                     for j in range(len(sel))]
            suf = _common_suffix([cs[i] for i in sel if cs[i]])
            for l in lens:
                for tl in range(min(len(suf), 2 * l) + 1):
                    tail = tuple(suf[len(suf) - tl:]) if tl else ()
                    for code in CODES:
                        for stp in STEPS:
                            got = _try_parse(q, h, side, other, occ, cs, sel,
                                             l, 0, tail, seeds, min_chain,
                                             code=code, step=stp,
                                             plens=plens,
                                             ptmpl=((u, a, b),))
                            if got is None or got[0].key() in seen:
                                continue
                            seen.add(got[0].key())
                            got[0].templated = True
                            if not fit_far(got[0], occ):
                                continue
                            found.append(got)


def _tail_cands(strs, l, cap=6, min_frac=0.15):
    """Candidate TERMINATORS off the WHOLE group rather than off its common
    suffix.

    `_common_suffix` is the right reading when the terminator is the thing
    every member of one constant-far-side group ends with; it returns the
    EMPTY suffix as soon as two members end differently, which is exactly what
    a complete width class looks like -- a class that spells every digit at
    every position ends every way it can.  The dev fixture of the weight
    sequence (`1RB---_0LB1RC_1LB0RD_1LC0RD` at B1/R) has one
    constant-far-side group covering all 900 anchor visits, a common suffix of
    length ZERO, and a terminator of `11`.  LADDER_NOFAM.md's fourth
    unchanged defect, from the side it actually bites on."""
    if not strs:
        return [()]
    n = len(strs)
    got = []
    for t in range(1, 2 * l + 3):
        c = Counter(tuple(x[len(x) - t:]) for x in strs if len(x) >= t)
        for suf, k in c.most_common(2):
            if k >= min_frac * n:
                got.append((k, suf))
    got.sort(key=lambda x: (-x[0], len(x[1])))
    out = [()]
    for _, s in got[:cap]:
        if s not in out:
            out.append(s)
    return out


def _weights_pass(q, h, side, full, seeds, lens, min_chain,
                  found, seen, max_other=1, max_occ=900, deadline=None):
    """The counter's NUMERATION, read not assumed -- the fifth instance of the
    rule 4e states and 4g restates.

    `Fam.decode` sums `d_i * b**i`.  Replace `b**i` by the sequence the machine
    itself states and six rows of the fifteen are Fibonacci, two more are a
    redundant base over cell pairs (`1,1,2,2,4,4` and `1,1,3,3,9,9`), and
    `base-b` is the case `w_i = b**i` and does not move.

    Three things are read here and each is checked rather than assumed:
    the WEIGHTS (`fit_weights`), the CANONICAL FORM (`fit_classes` -- without
    it `of_value` cannot produce the machine's own spelling, and 4g's
    positional-rebuild bug comes straight back), and the terminator off the
    whole group (`_tail_cands`).  The near-head prefix runs past the digit
    width on purpose: `p in range(l)` means a one-cell digit never gets one.

    The STEP is not varied.  With the weights read rather than assumed, `w`
    and `s*w` describe the same family -- the step and the weight sequence are
    the SAME axis -- so the pass fixes `s = 1` and lets the scale come out in
    the weights.  That is a reduction, not a restriction.

    The window is the FIRST `max_occ` visits, not the last: the passes above
    take `occ[-200:]`, which is the right window for a chain test and the wrong
    one for a numeration, because a counter's narrow width classes are all at
    the START of the run and the canonical form is read off the narrow ones.
    A walk that begins at width 8 has no base case to generalize from."""
    occ = full[:max_occ]
    cs, os = [], []
    for _, s in occ:
        c = runs_cells(s[2] if side == 'L' else s[3])
        o = runs_cells(s[3] if side == 'L' else s[2])
        cs.append(c)
        os.append(tuple(o) if o is not None else None)
    pop = Counter(o for o in os if o is not None)
    for other, n in pop.most_common(max_other):
        if n < min_chain:
            break
        sel = [i for i in range(len(occ)) if os[i] == other]
        strs = [cs[i] for i in sel if cs[i]]
        for l in lens[:2]:
            for tail in _tail_cands(strs, l):
                for p in range(l + 2):
                    if deadline and time.time() > deadline:
                        return
                    grams, _ = _grams(cs, sel, l, p, tail)
                    alpha = sorted({x for g in grams if g for x in g})
                    if not (2 <= len(alpha) <= 3):
                        continue
                    for perm in itertools.permutations(alpha):
                        idx = {a: i for i, a in enumerate(perm)}
                        ds = [None if g is None or any(x not in idx for x in g)
                              else tuple(idx[x] for x in g) for g in grams]
                        obs, sn = {}, set()
                        for d in ds:
                            if not d or d in sn:
                                continue
                            sn.add(d)
                            obs.setdefault(len(d), []).append(d)
                        # free pre-filter, before the rational elimination:
                        # the widths have to be contiguous from 1 and the
                        # classes have to grow, or there is no numeration to
                        # read.  This is `numsys.py`'s statistic, used as a
                        # gate rather than as a label.
                        ks = sorted(obs)
                        if len(ks) < 4 or ks != list(range(1, ks[-1] + 1)):
                            continue
                        w = fit_weights([d for d in ds if d])
                        if w is None or all(x == len(perm) ** i
                                            for i, x in enumerate(w)):
                            continue     # positional: the plain pass owns it
                        cls = fit_classes(obs)
                        if cls is None:
                            continue
                        got = _try_parse(q, h, side, other, occ, cs, sel,
                                         l, p, tail, seeds, min_chain,
                                         weights=w, classes=cls)
                        if got is None or got[0].key() in seen:
                            continue
                        seen.add(got[0].key())
                        found.append(got)


def _widths(named, mult=3, cap=4):
    """Candidate digit widths.  A carry rule that shifts ONE CELL per
    application names width 1 even when the counter's digit is two cells
    wide -- the carry crosses the digit in pieces.  So the widths the ladder
    offers are its own run-word widths and small MULTIPLES of them; the
    alphabet is still read off the ladder, never from a list."""
    ws = {len(w) for w in named} or {1}
    return sorted({m * w for w in ws for m in range(1, mult + 1)
                   if m * w <= cap})


def _common_suffix(seqs):
    if not seqs:
        return []
    out = []
    for i in range(1, min(len(s) for s in seqs) + 1):
        col = {tuple(s[len(s) - i:]) for s in seqs}
        if len(col) != 1:
            break
        out = list(seqs[0][len(seqs[0]) - i:])
    return out


def _grams(cs, sel, l, p, tail, plens=None):
    """Digit tuples and near-head prefixes per selected visit.

    `plens` gives the prefix length PER VISIT rather than one for all of them,
    which is what a prefix `u^(a*p+b)` needs: the spacer grows with the lap, so
    the number of cells to strip before the digits do."""
    grams, pres = [], []
    for j, i in enumerate(sel):
        c = cs[i]
        pj = p if plens is None else plens[j]
        if c is None or pj is None or len(c) < pj + len(tail):
            grams.append(None)
            pres.append(None)
            continue
        pres.append(PTMPL if plens is not None else tuple(c[:pj]))
        mid = None
        for pad in range(l + len(tail) + 1):
            cc = list(c) + [0] * pad
            n = len(cc) - pj - len(tail)
            if n < 0 or n % l:
                continue
            if tail and tuple(cc[len(cc) - len(tail):]) != tail:
                continue
            mid = cc[pj:pj + n]
            break
        if mid is None:
            grams.append(None)
            continue
        grams.append(tuple(tuple(mid[j:j + l]) for j in range(0, len(mid), l)))
    return grams, pres


def _try_parse(q, h, side, other, occ, cs, sel, l, p, tail, seeds, min_chain,
               code='binary', step=1,
               pids=None, weights=None, classes=None,
               plens=None, ptmpl=None, unary=False):
    grams, pres = _grams(cs, sel, l, p, tail, plens)
    alpha = set()
    for g in grams:
        if g:
            alpha |= set(g)
    # `unary` selects the one-digit reading and NOTHING else, so the pass that
    # asks for it cannot also re-find the readings the passes above already
    # tried.
    if unary != (len(alpha) == 1):
        return None
    # The guard used to be `2 <= len(alpha)`.  A UNARY counter -- one digit
    # word, `word^p`, the value IS the run count -- was rejected here before
    # any base, code, step or terminator was tried, which is upstream of every
    # axis 4e, 4f and 4g added.  It is not a degenerate radix, it is a
    # different constructor, and `b = 1` states it exactly: `maxval(k)` is 0,
    # so every string is the top, so the successor is always the FILL and the
    # interior/overflow split collapses to one arm per phase.  The kernel says
    # the same thing with no change at all -- `fam_is_top` at `fm_b = 1` is
    # `1^k - 1 < 0 + fm_step`, which is true for every string.
    #
    # It is also the WEAKEST reading in the file: a bare run of `1`s inside a
    # bouncer gives a monotone run count too, which is why `nofam.unary_probe`
    # ranks on the far side and the phase set rather than on how big p gets.
    # So it is asked for explicitly and only after every other reading has
    # declined the row -- measured, letting it run in the ordinary pass
    # suppressed the Fibonacci reading of `1RB0RB_0LC1RD_1LC1LA_0LA1RB` and
    # gave eleven families to the BBB(4) champion, which is not a counter.
    if not (1 <= len(alpha) <= 3):
        return None
    if unary and (code != 'binary' or weights is not None
                  or ptmpl is not None):
        return None                  # a reflected code over one digit is one
    # accept either a digit word the ladder names outright, or a digit WIDTH
    # the ladder names -- the latter only on a chain twice as long, since the
    # +1 evidence is then carrying the whole alphabet claim
    strong = any(a in seeds for a in alpha)
    need = min_chain if strong else 2 * min_chain
    best = None
    for perm in itertools.permutations(sorted(alpha)):
        idx = {a: i for i, a in enumerate(perm)}
        b = len(perm)
        vals = []
        for g, pr in zip(grams, pres):
            if g is None or pr is None or any(x not in idx for x in g):
                vals.append(None)
                continue
            dsx = [idx[x] for x in g]           # LSB-first
            if b == 1:
                # the RUN COUNT is the value: p and v collapse, so the fill law
                # has nothing to infer and the width is the whole parameter
                v = len(dsx)
            elif weights is not None:
                if len(dsx) > len(weights):
                    vals.append(None)
                    continue
                v = sum(d * weights[i] for i, d in enumerate(dsx))
            else:
                if code == 'gray':
                    dsx = gray_decode(dsx, b)
                v = 0
                for d in reversed(dsx):
                    v = v * b + d
            vals.append((v, pr, len(g)))
        if weights is not None:
            def _mx(k, w=weights, bb=b):
                return sum((bb - 1) * w[i] for i in range(min(k, len(w))))
        elif b == 1:
            def _mx(k):
                return 0
        else:
            def _mx(k, bb=b):
                return bb ** k - 1
        i = 0
        while i < len(vals):
            if vals[i] is None:
                i += 1
                continue
            k = i
            while k + 1 < len(vals) and vals[k + 1] is not None \
                    and vals[k + 1][1] == vals[i][1]:
                if pids is None or pids[k + 1] == pids[k]:
                    if vals[k + 1][0] != vals[k][0] + step:
                        break
                elif vals[k][0] + step <= _mx(vals[k][2]):
                    # p may only move at the top string -- that is what makes
                    # the fill the only arm crossing the outer parameter
                    break
                k += 1
            if k - i + 1 >= need and (best is None or k - i + 1 > best[2]):
                nm = {a: seeds[a] for a in perm if a in seeds}
                fm = Fam(q, h, side, other, list(perm),
                         () if ptmpl else vals[i][1], nm, tail)
                fm.code, fm.step = code, step
                fm.weights, fm.classes = weights, classes
                fm.ptmpl = ptmpl
                best = (fm, occ[sel[i]][0], k - i + 1)
            i = k + 1
    return best


def kmax_for(b, budget=500):
    """Widest counter enumerated exhaustively inside a fixed string budget."""
    k, tot = 0, 0
    while tot + b ** (k + 1) <= budget and k < 7:
        k += 1
        tot += b ** k
    return max(k, 2)


def probe_families(tm, snaps, rules, top=4, max_occ=200):
    """Near-miss diagnostic for rows where no family is accepted: for the best
    reading of each frequent anchor, the HISTOGRAM of value deltas between
    consecutive visits.  A row whose modal delta is +1 but whose chain breaks
    is a counter the odometer model does not fit; a row with no dominant delta
    is not a counter segment at that anchor at all.  Discovery only."""
    named = digit_words(rules)
    seeds = set()
    for w in named:
        seeds |= rots(w)
    lens = _widths(named)
    byqh = defaultdict(list)
    for t, s in snaps:
        if s is None:
            break
        byqh[(s[0], s[1])].append((t, s))
    out = []
    for (q, h), occ in sorted(byqh.items(),
                              key=lambda kv: -len(kv[1]))[:top]:
        occ = occ[-max_occ:]
        for side in ('L', 'R'):
            cs = [runs_cells(s[2] if side == 'L' else s[3]) for _, s in occ]
            os = [tuple(runs_cells(s[3] if side == 'L' else s[2]) or ())
                  for _, s in occ]
            for other, n in Counter(os).most_common(2):
                sel = [i for i in range(len(occ)) if os[i] == other]
                if len(sel) < 6:
                    continue
                suf = _common_suffix([cs[i] for i in sel if cs[i]])
                for l in lens:
                    for tl in range(min(len(suf), 2 * l) + 1):
                        tail = tuple(suf[len(suf) - tl:]) if tl else ()
                        for pp in range(l):
                            g, _ = _grams(cs, sel, l, pp, tail)
                            al = set()
                            for x in g:
                                if x:
                                    al |= set(x)
                            if not (2 <= len(al) <= 3):
                                continue
                            for perm in itertools.permutations(sorted(al)):
                                idx = {a: i for i, a in enumerate(perm)}
                                vs = []
                                for x in g:
                                    if x is None or any(y not in idx
                                                        for y in x):
                                        vs.append(None)
                                        continue
                                    v = 0
                                    for y in reversed(x):
                                        v = v * len(perm) + idx[y]
                                    vs.append(v)
                                d = Counter(b - a for a, b in zip(vs, vs[1:])
                                            if a is not None and b is not None)
                                if not d:
                                    continue
                                tot = sum(d.values())
                                out.append({
                                    'anchor': '%s%d' % (chr(65 + q), h),
                                    'side': side, 'digit_len': l,
                                    'base': len(perm), 'terminator_len': tl,
                                    'prefix_len': pp, 'visits': tot,
                                    'plus1_frac': round(d.get(1, 0) / tot, 3),
                                    'top_deltas': d.most_common(3)})
    if out:
        out.sort(key=lambda r: -r['plus1_frac'])
        return out[:6]
    # No reading at all.  The commonest cause is that the FAR side never
    # repeats -- it grows with the counter, so the family would need a second
    # parameter E(p, v) and a one-parameter CTR cannot express it.  Report the
    # largest constant-far-side group per anchor so the two cases separate.
    info = []
    for (q, h), occ in sorted(byqh.items(), key=lambda kv: -len(kv[1]))[:top]:
        occ = occ[-max_occ:]
        for side in ('L', 'R'):
            os = [tuple(runs_cells(s[3] if side == 'L' else s[2]) or ())
                  for _, s in occ]
            c = Counter(os)
            info.append({'anchor': '%s%d' % (chr(65 + q), h), 'side': side,
                         'visits': len(occ),
                         'max_constant_far_side_group':
                             c.most_common(1)[0][1] if c else 0})
    info.sort(key=lambda r: -r['max_constant_far_side_group'])
    return [{'no_reading': True, 'far_side_groups': info[:4]}]


# ---------------------------------------------------------------------- arms

_UID = itertools.count()


class Arm:
    def __init__(self, name, rule, ops, kind, uses):
        self.name, self.rule, self.ops = name, rule, ops
        self.kind, self.uses = kind, uses
        self.covers = []
        # a stable identity for the subsumption cache: arm NAMES restart with
        # the counter on each candidate family, so they cannot key it
        self.uid = next(_UID)
        self.multi_var = _multi_var(rule.lhs)

    def steps(self, env):
        tot = Expr(0)
        for e in self.rule.fired.values():
            tot = tot + e
        return tot.subst(env)

    def json(self):
        return {'name': self.name, 'kind': self.kind,
                'lhs': cfg_repr(self.rule.lhs), 'rhs': cfg_repr(self.rule.rhs),
                'lbs': dict(self.rule.lbs),
                'fired': {'%s%d' % (chr(65 + t[0]), t[1]): repr(e)
                          for t, e in sorted(self.rule.fired.items())},
                'steps': repr(self.steps({})),
                'ops': self.ops, 'uses_ladder_rules': sorted(self.uses),
                'covers_examples': self.covers[:6]}


def sample_digits(fam, kmax=5, extra=(6, 7, 8, 9)):
    """[(phase, digit string)] the arms are mined from."""
    out = []
    for ph in range(len(fam.tails)):
        for k in range(1, kmax + 1):
            if fam.weights is not None:
                out.extend((ph, list(ds)) for _, ds in fam.klass(k))
                continue
            for v in range(fam.b ** k):
                ds = []
                x = v
                for _ in range(k):
                    ds.append(x % fam.b)
                    x //= fam.b
                out.append((ph, ds))
        for k in extra:
            if fam.weights is not None:
                # a pseudo-random digit string is not a member of a family
                # whose representation is canonical; the class itself is small
                # (Fibonacci sizes), so sample its two ends instead
                cl = fam.klass(k)
                out.extend((ph, list(ds)) for _, ds in cl[:2] + cl[-2:])
                continue
            for seed in (0, 1, 2):
                ds = [(i * 7 + seed * 3 + k) % fam.b for i in range(k)]
                out.append((ph, ds))
        # the TOP string at every width, and where the fill law sends it.  The
        # fill arm is generalized across these, so they have to be in the
        # sample at more widths than the exhaustive part reaches -- one
        # instance is a base case, several are an induction.
        f = fam_fill(fam, ph)
        for k in range(1, 13):
            t = fam.top(k)
            if t:
                out.append((ph, t))
            t = f.apply(k)
            if t:
                out.append((f.to, t))
    return out


def _vkey(v):
    return (v[0], v[1], tuple(w for w, _ in v[2]), tuple(w for w, _ in v[3]))


def _groups(fam, windows, max_exact_runs=4):
    """key -> [((ds, p), view)] over the sampled states.

    Sampling several p is what puts the OUTER parameter into the arms
    symbolically: `_generalize` turns any coordinate that differs across the
    instances into a free variable, so a far-side run that moves with p comes
    out of the same machinery that already generalizes the counter's own runs.
    One p would pin it, which is the one-parameter family."""
    g = defaultdict(list)
    ps = fam.psample()
    for ph, ds in sample_digits(fam):
        for pp in ps:
            cfg = fam.cfg(ds, pp, ph)
            if cfg is None:
                continue
            for m in windows:
                v = fam.view(cfg, m)
                g[_vkey(v)].append((((ds, pp, ph)), v))
            # The exact view is what the FILL arm needs -- it has to see the
            # counter's END.  The bound is on the DIGIT runs: the near-head
            # prefix and the phase's terminator are fixed cells that add runs
            # without adding generality, and a phase whose terminator is four
            # cells long was silently denied a fill arm by counting them.
            fixed = len(fam.pre) + len(fam.tails[ph])
            if len(fam.counter_side(cfg)) <= max_exact_runs + fixed:
                v = fam.view(cfg, 0, marker=False)  # exact: the overflow arm
                g[_vkey(v)].append((((ds, pp, ph)), v))
    return g


def mine_arms(tm, rules, fam, windows=(1, 2, 3, 4, 5), max_keys=160,
              budget=400, deadline=None, ctr=None, groups=None):
    """Group canonical family configs by local-view shape, generalize counts
    across instances, and replay each generalization to the next anchor."""
    groups = groups if groups is not None else _groups(fam, windows)
    ranked = sorted(groups.items(), key=lambda kv: -len(kv[1]))[:max_keys]
    arms, seen = [], set()
    ctr = ctr if ctr is not None else itertools.count()
    for key, insts in ranked:
        if deadline and time.time() > deadline:
            break
        lhs, lbs = _generalize(insts)
        if lhs is None:
            continue
        sig = (key, tuple(repr(e) for e in cfg_counts(lhs)))
        if sig in seen:
            continue
        seen.add(sig)
        for arm in _replay_arm(tm, rules, fam, lhs, lbs, next(ctr), budget,
                               deadline=deadline):
            arms.append(arm)
            break
    return arms


def repair(tm, rules, fam, arms, uncovered, ctr, groups, budget=400,
           deadline=None, windows=(2, 3, 4, 5, 6, 1), max_new=16,
           pins=(1, 2, 3, 10 ** 9)):
    """Specialize on demand -- the induction's BASE CASES.

    A digit string is left uncovered when some run count sits below the lower
    bound the symbolic arm inherited from the ladder rule it bulk-applies
    (r1 needs two blocks to drain, so the symbolic carry arm only starts at
    j >= 3).  The repair PINS the coordinates that are small and keeps the
    rest symbolic, re-generalizing over the sample instances that agree on
    the pinned coordinates.  The result is one arm per small carry index --
    concrete replay at small j, exactly the base case of the induction whose
    step case is the symbolic arm."""
    rep = Replay(tm, [], budget=4, raise_ok=False)
    added = []
    order, n_added = order_arms(arms), 0
    for item in uncovered:
        k, v = item[0], item[1]
        pp = item[2] if len(item) > 2 else fam.p0
        ph = item[3] if len(item) > 3 else 0
        if len(added) >= max_new or (deadline and time.time() > deadline):
            break
        ds = fam.of_value(v, k)      # in the family's CODE, not positional
        if ds is None:
            continue
        nd, npp, nph = succ(fam, ds, pp, ph)
        cfg = fam.cfg(ds, pp, ph)
        nxt = None if nd is None else fam.cfg(nd, npp, nph)
        if cfg is None or nxt is None:
            continue
        want = cfg_cells(nxt)
        if len(added) != n_added:
            order, n_added = order_arms(arms + added), len(added)
        first = None
        for a in order:
            if rep.apply_rule(a.rule, cfg, bulk=False) is not None:
                first = a
                break
        if first is not None and \
                cfg_cells(rep.apply_rule(first.rule, cfg, bulk=False)) == want:
            continue
        got = None
        for m in windows:
            # the deadline used to be checked once per ITEM, and one item can
            # try 6 windows x 2 markers x 4 pins replays: measured at 98.8 s
            # against a 90 s deadline on 1RB---_0LC1RD_1LB1RC_1LB0RD, which
            # is how a cooperative cap turns into a hard timeout once the
            # round is repeated per candidate
            if deadline and time.time() > deadline:
                break
            for mk in (True, False):
                view = fam.view(cfg, m, marker=mk)
                key = _vkey(view)
                cs = [e.c for e in cfg_counts(view)]
                for T in pins:
                    if deadline and time.time() > deadline:
                        break
                    pin = {i for i, c in enumerate(cs) if c <= T}
                    insts = [(d, w) for d, w in groups.get(key, [])
                             if all(cfg_counts(w)[i].c == cs[i] for i in pin)]
                    lhs, lbs = _generalize(insts + [((ds, pp, ph), view)],
                                           pin)
                    if lhs is None:
                        continue
                    # try EVERY anchor stop the replay offers, not just the
                    # first: past a fill the family member is several anchor
                    # visits along, and taking the first stop is exactly how
                    # an arm lands off the family.
                    for arm in _replay_arm(tm, rules, fam, lhs, lbs,
                                           next(ctr), budget,
                                           deadline=deadline):
                        out = rep.apply_rule(arm.rule, cfg, bulk=False)
                        if out is not None and cfg_cells(out) == want:
                            got = arm
                            break
                    if got:
                        break
                if got:
                    break
            if got:
                break
        if got:
            added.append(got)
    return added


def _generalize(insts, pin=()):
    counts = [cfg_counts(v) for _, v in insts]
    n = len(counts[0])
    if any(len(c) != n for c in counts):
        return None, None
    out, lbs, vi = [], {}, 0
    for i in range(n):
        vals = [c[i].c for c in counts]
        if i in pin or len(set(vals)) == 1:
            out.append(Expr(vals[0]))
        else:
            var = 'y%d' % vi
            vi += 1
            lbs[var] = 0
            out.append(Expr(min(vals), {var: 1}))
    if vi == 0:
        out = list(out)
    proto = insts[0][1]
    q, h, L, R = proto
    nl = len(L)
    lhs = (q, h,
           tuple((L[i][0], out[i]) for i in range(nl)),
           tuple((R[i][0], out[nl + i]) for i in range(len(R))))
    return lhs, lbs


def _member_env(fam, cfg, lbs, tries=3):
    """Membership of a SYMBOLIC landing config: check it at the free
    variables' lower bounds and a couple of offsets.  All instantiations must
    be members -- one mid-digit witness is enough to reject the stop."""
    vs = sorted({v for e in cfg_counts(cfg) for v in e.v})
    if not vs:
        return fam.member(cfg)
    for d in range(tries):
        env = {v: lbs.get(v, 1) + d for v in vs}
        if not fam.member(cfg, env):
            return False
    return True


def _replay_arm(tm, rules, fam, lhs, lbs, idx, budget, max_stops=6,
                deadline=None):
    """Replay to the anchor, yielding at each stop.

    It used to yield only the FIRST anchor-shaped config and return.  An
    increment crosses the anchor cell several times, so the first stop is
    frequently a mid-flight tape rather than a family member -- and past a
    fill, where the counter widens, the family member is several visits
    further on.  Now the member stops come first, and the raw first stop is
    kept only as the fallback, so nothing that used to replay stops doing so."""
    rep = Replay(tm, rules, lbs=dict(lbs), budget=budget)
    cur = rep.step(lhs)
    if cur is None:
        return
    ops, uses, n, stops, fallback = ['step'], set(), 0, 0, None
    while cur is not None and n < budget:
        n += 1
        # a single replay is `budget` engine steps over configs that can be
        # large, so the step budget alone does not bound the WALL clock; every
        # caller has a deadline and this is where it has to be honoured
        if deadline and not n % 16 and time.time() > deadline:
            break
        if fam.anchor_shaped(cur):
            rule = Rule('arm%d' % idx, lhs, cur, dict(rep.lbs), None,
                        dict(rep.fired), level=1)
            kind = 'local' if any(w == MARKER for w, _ in
                                  fam.counter_side(cur)) else 'global'
            arm = Arm('arm%d' % idx, rule, list(ops), kind, set(uses))
            stops += 1
            if _member_env(fam, cur, rep.lbs):
                yield arm
            elif fallback is None:
                fallback = arm
            if stops >= max_stops:
                break
        nxt = None
        for ru in rules:
            nxt = rep.apply_rule(ru, cur)
            if nxt is not None:
                ops.append('bulk:' + ru.name)
                uses.add(ru.name)
                break
        if nxt is None:
            nxt = rep.chain(cur)
            if nxt is not None:
                ops.append('chain')
        if nxt is None:
            nxt = rep.step(cur)
            if nxt is not None:
                ops.append('step')
        cur = nxt
    if fallback is not None:
        yield fallback


# ------------------------------------------------------------------ coverage

def spec_key(arm):
    """Deterministic TIE-BREAK inside `order_arms`, and nothing more.

    It used to be the case split itself, and it put the most general arm of a
    shape first, which is how an arm that is right on the bulk and wrong on
    the fill shadowed every specialization the repair could build for it.  The
    order is now `order_arms` -- a linearization of pattern subsumption, most
    specific first -- and this is only how ties among incomparable patterns
    are broken."""
    q, h, L, R = arm.rule.lhs
    runs = L + R
    local = any(w == MARKER for w, _ in runs)
    nv = len({v for e in cfg_counts(arm.rule.lhs) for v in e.v})
    return (1 if local else 0, len(runs), -nv, arm.name)


def _count_covers(ae, la, be, lb):
    """Does pattern count `ae` (lower bounds `la`) match every value pattern
    count `be` (lower bounds `lb`) matches?

    A pattern coordinate is either a constant -- it matches that value alone --
    or `c + var` with `var >= lbs[var]`, which matches every value from
    `c + lbs[var]` up.  Both are intervals, so containment is arithmetic."""
    def floor(e, lbs):
        if e.is_const():
            return e.c, e.c                      # exactly this value
        items = list(e.v.items())
        if len(items) != 1 or items[0][1] != 1:
            return None, None                    # not a shape match_rule takes
        return e.c + lbs.get(items[0][0], 1), None
    alo, aex = floor(ae, la)
    blo, bex = floor(be, lb)
    if alo is None or blo is None:
        return False
    if aex is not None:                          # a is a single value
        return bex is not None and bex == aex
    return blo >= alo                            # b's whole range is inside a's


def _side_covers(pa, la, pb, lb):
    amark = bool(pa) and pa[-1][0] == MARKER
    bmark = bool(pb) and pb[-1][0] == MARKER
    ax = pa[:-1] if amark else pa
    bx = pb[:-1] if bmark else pb
    if amark:
        if len(ax) > len(bx):
            return False        # a demands more runs than b guarantees
    elif bmark or len(ax) != len(bx):
        return False            # an exact pattern cannot cover an open one
    for (aw, ae), (bw, be) in zip(ax, bx):
        if aw != bw or not _count_covers(ae, la, be, lb):
            return False
    return True


def _multi_var(lhs):
    """A variable used in two coordinates ties them together, which is outside
    the interval reasoning above; such an arm is treated as incomparable."""
    seen = Counter()
    for e in cfg_counts(lhs):
        for v in e.v:
            seen[v] += 1
    return any(n > 1 for n in seen.values())


_COVERS = {}


def covers(a, b):
    """Is every config arm `b` applies to also one arm `a` applies to?

    Applicability is `match_rule` plus the lower-bound check in
    `Replay.apply_rule`, both syntactic, so this is decidable on the arms as
    data -- which is the point: the case split has to be checkable by whatever
    checks the certificate, not just by the search that produced it.

    Memoized on the pair: `order_arms` is quadratic and runs inside `cover`
    and `repair`, so the same comparison is asked thousands of times per row."""
    key = (a.uid, b.uid)
    r = _COVERS.get(key)
    if r is None:
        _COVERS[key] = r = _covers(a, b)
    return r


def _covers(a, b):
    qa, ha, La, Ra = a.rule.lhs
    qb, hb, Lb, Rb = b.rule.lhs
    if (qa, ha) != (qb, hb):
        return False
    if a.multi_var or b.multi_var:
        return a is b
    la, lb = a.rule.lbs, b.rule.lbs
    return _side_covers(La, la, Lb, lb) and _side_covers(Ra, la, Rb, lb)


def strictly_covers(a, b):
    return a is not b and covers(a, b) and not covers(b, a)


def order_arms(arms):
    """THE CASE SPLIT: first applicable in this order, most specific first.

    The order is a linearization of pattern subsumption -- if arm `a`'s
    pattern matches everything arm `b`'s does and more, `b` comes first -- with
    `spec_key` breaking ties between incomparable patterns.  That is ordinary
    pattern-match semantics, and it is correct BY CONSTRUCTION in the sense
    that matters for Stage B: the checker re-derives the order from the arms
    themselves (`order_ok`) rather than trusting the order they were written
    in, and it never has to decide whether an arm's RESULT is in the family.

    The alternative considered was `first applicable whose result is a family
    member`, which is also decidable; it was rejected because it does not
    actually settle the case it was proposed for -- an interior arm firing at
    an overflow lands a whole carry short, i.e. ON a member, just the wrong
    one -- and it puts a membership decision inside the kernel's case split.
    Subsumption order costs the checker one syntactic comparison per pair."""
    rest, out = list(arms), []
    while rest:
        cand = [a for a in rest
                if not any(strictly_covers(a, b) for b in rest)]
        if not cand:                     # subsumption is a preorder: no cycles
            out.extend(sorted(rest, key=spec_key))
            break
        a = min(cand, key=spec_key)
        out.append(a)
        rest.remove(a)
    return out


def order_ok(arms):
    """The property `order_arms` establishes, stated so a checker can re-run
    it: no arm is preceded by one strictly more general."""
    return not any(strictly_covers(arms[i], arms[j])
                   for i in range(len(arms)) for j in range(i + 1, len(arms)))


def only_at_overflow(fam, strings):
    """Are these digit strings exactly the top ones -- the fill?"""
    return bool(strings) and all(v == fam.maxval(k) for k, v in strings)


def _fam_cfg(fam, ds, pp):
    return fam.cfg(ds, pp)


def all_strings(fam, kmax):
    """Every member of every width up to kmax.  With a weight sequence that is
    the CANONICAL strings only -- enumerating all b**k would report uncovered
    members the machine never reaches, which is `cover`'s own warning read from
    the other side."""
    out = []
    for k in range(1, kmax + 1):
        if fam.weights is not None:
            out.extend(list(ds) for _, ds in fam.klass(k))
            continue
        for v in range(fam.b ** k):
            ds, x = [], v
            for _ in range(k):
                ds.append(x % fam.b)
                x //= fam.b
            out.append(ds)
    return out


def all_states(fam, kmax):
    return [(ds, pp, ph) for ds in all_strings(fam, kmax)
            for pp in fam.psample() for ph in range(len(fam.tails))]


def reach(fam, boot_ds, boot_p, kmax, cap=4000, boot_ph=0):
    """The states the machine actually VISITS: walk the successor from the
    boot.  With a fill law that widens by more than one, the widths reachable
    from the boot are one parity class -- and demanding coverage of the other
    parity demands arms for configurations the run never enters.  (That is the
    `..._at_octave_parity_0` gate label, read from this side.)"""
    out, seen = [], set()
    ds, pp, ph = list(boot_ds), boot_p, boot_ph
    while ds is not None and len(ds) <= kmax and len(out) < cap:
        key = (len(ds), fam.value(ds), pp, ph)
        if key in seen:
            break
        seen.add(key)
        out.append((list(ds), pp, ph))
        ds, pp, ph = succ(fam, ds, pp, ph)
    return out


def cover(tm, fam, arms, kmax=7, states=None):
    """Every digit string in `states` (default: all up to kmax digits): the
    FIRST APPLICABLE arm in `order_arms` order must land on the successor.
    Returns (ok, covmap, report).

    `shadowed` counts the failures where the selected arm lands wrong and a
    LATER arm lands right -- the case the old most-general-first order made
    unreachable, measured rather than asserted."""
    rep = Replay(tm, [], budget=4, raise_ok=False)
    arms = order_arms(arms)
    uncovered, wrong, used = [], [], defaultdict(int)
    covmap = defaultdict(set)
    total, shadowed = 0, 0
    for ds, pp, ph in (all_states(fam, kmax) if states is None else states):
        nd, npp, nph = succ(fam, ds, pp, ph)
        if nd is None:
            continue
        k, v = len(ds), fam.value(ds)
        total += 1
        cfg = fam.cfg(ds, pp, ph)
        nxt = fam.cfg(nd, npp, nph)
        if cfg is None or nxt is None:
            continue
        want = cfg_cells(nxt)
        hit = 0
        for i, arm in enumerate(arms):
            out = rep.apply_rule(arm.rule, cfg, bulk=False)
            if out is None:
                continue
            if cfg_cells(out) != want:
                wrong.append((arm.name, k, v, pp, ph))
                for later in arms[i + 1:]:
                    o2 = rep.apply_rule(later.rule, cfg, bulk=False)
                    if o2 is not None and cfg_cells(o2) == want:
                        shadowed += 1
                        break
                break
            hit += 1
            used[arm.name] += 1
            covmap[arm.name].add((k, v, pp, ph))
            if len(arm.covers) < 8:
                arm.covers.append(v)
            break
        if hit == 0 and (not wrong or wrong[-1][1:] != (k, v, pp, ph)):
            uncovered.append((k, v, pp, ph))
    ok = not uncovered and not wrong
    return ok, covmap, {'strings': total, 'kmax': kmax,
                'uncovered': uncovered[:12], 'n_uncovered': len(uncovered),
                'uncovered_all': uncovered,
                'wrong': wrong[:12], 'n_wrong': len(wrong),
                'wrong_all': [(k, v, pp, ph) for _, k, v, pp, ph in wrong],
                'shadowed_by_selection': shadowed,
                'wrong_only_at_overflow': only_at_overflow(
                    fam, [(k, v) for _, k, v, _, _ in wrong]),
                'fails_only_at_overflow': only_at_overflow(
                    fam, [(k, v) for k, v, _, _ in uncovered]
                    + [(k, v) for _, k, v, _, _ in wrong]),
                'arm_hits': dict(used)}


def prune(tm, fam, arms, kmax, states=None, deadline=None):
    """Drop any arm the family still covers correctly without: the window
    sweep leaves whole-side variants of arms whose local form already does
    the job.  Least-used first, one re-check per drop -- so it is one full
    coverage pass per arm, which is why it takes a deadline."""
    ok, covmap, _ = cover(tm, fam, arms, kmax, states)
    if not ok:
        return arms
    for a in sorted(arms, key=lambda a: len(covmap.get(a.name, ()))):
        if len(arms) == 1 or (deadline and time.time() > deadline):
            break
        trial = [x for x in arms if x is not a]
        ok2, cov2, _ = cover(tm, fam, trial, kmax, states)
        if ok2:
            arms, covmap = trial, cov2
    return arms


def drop_wrong(tm, fam, arms, kmax, states=None, rounds=4):
    """Remove arms that claim a config and land OFF the family.

    Under the old most-general-first order this was the only move that could
    unshadow a repair.  `order_arms` puts the specialization first outright,
    so this now only fires for an arm that is wrong on a string NO other arm
    claims correctly.  Dropping the offender is the one move that keeps the selection a
    function of the configuration: it only ever removes arms, so an arm set
    that already covers is untouched, and what the offender was covering is
    handed back to the repair as ordinary uncovered strings."""
    ok, _, rep = cover(tm, fam, arms, kmax, states)
    for _ in range(rounds):
        if ok or not rep['n_wrong']:
            break
        bad = Counter(w[0] for w in rep['wrong'])
        name = bad.most_common(1)[0][0]
        trial = [a for a in arms if a.name != name]
        if not trial:
            break
        ok2, _, rep2 = cover(tm, fam, trial, kmax, states)
        if rep2['n_wrong'] + rep2['n_uncovered'] > \
                rep['n_wrong'] + rep['n_uncovered']:
            break
        arms, ok, rep = trial, ok2, rep2
    return arms


def minimize(arms, covmap):
    """Greedy set cover: drop arms whose every digit string is already claimed
    by a more general one (the window sweep yields many nested variants)."""
    need = set()
    for s in covmap.values():
        need |= s
    kept = []
    for a in sorted(arms, key=lambda a: -len(covmap.get(a.name, ()))):
        gain = covmap.get(a.name, set()) & need
        if gain:
            kept.append(a)
            need -= gain
    return kept


# ---------------------------------------------------------------------- boot

def visited_states(tm, upto):
    """States the machine actually visits in the first `upto` steps -- the
    Visited conjunct of BBB4_Statement.QuasiHaltsSt.  Never-visited states do
    not witness quasi-halting, so never-QH is  visited == infinitely-often,
    not  all-states == infinitely-often."""
    tape, pos, q, out = {}, 0, 0, set()
    for _ in range(upto + 1):
        out.add(q)
        tr = tm.get((q, tape.get(pos, 0)))
        if tr is None:
            break
        w, d, q = tr
        tape[pos] = w
        pos += d
    return out


def find_boot(fam, snaps):
    """First trace index whose config IS a family member; its (ds, p, phase).
    """
    for t, s in snaps:
        if s is None:
            break
        pp = fam.far_p(s)
        if pp is None or (s[0], s[1]) != (fam.q, fam.h):
            continue
        c = runs_cells(fam.counter_side(s))
        if c is None:
            continue
        ph, ds = fam.read(c, pp)
        if not ds:
            continue
        cf = fam.cfg(ds, pp, ph)
        if cf is None or cfg_cells(cf) != cfg_cells(s):
            continue
        return t, ds, pp, ph
    return None, None, None, None


# ------------------------------------------------------- differential checks

def differential(tm, fam, arms, boot_ds, boot_p=None, n_checks=18,
                 max_steps=400000, max_visits=24, boot_ph=0):
    """Raw-simulator check of the FAMILY (not just the rules): from E(v), the
    raw machine must reach E(v+1), and -- the arms' fired counts being exact --
    at exactly the predicted step count.  Octave boundaries (v = b^m - 1 and
    v = b^m) are always among the probes.

    The head passes the anchor cell several times per increment, so the check
    scans the first `max_visits` (state, head) matches and reports WHICH one
    is E(v+1); requiring it to be the first would fail on every machine whose
    carry re-crosses its own low digit."""
    # Probes come off the REACHABLE walk, so they are states the machine
    # actually enters under the inferred fill law -- and every fill (the top
    # string of each width) is among them, plus the state either side of it.
    walk = reach(fam, boot_ds, fam.p0 if boot_p is None else boot_p,
                 kmax=9, cap=6000, boot_ph=boot_ph)
    tops = [i for i, (ds, _, _) in enumerate(walk)
            if all(d == fam.b - 1 for d in ds)]
    want_i = set()
    for i in tops:
        want_i |= {i - 1, i, i + 1}
    for i in (0, 1, 2, 5, 11, len(walk) // 2, len(walk) - 2):
        want_i.add(i)
    probes = [walk[i] for i in sorted(want_i)
              if 0 <= i < len(walk)][:n_checks]
    rep = Replay(tm, [], budget=4, raise_ok=False)
    order = order_arms(arms)
    out = []
    for ds, pp, ph in probes:
        v = fam.value(ds)
        nd, npp, nph = succ(fam, ds, pp, ph)
        cfg = fam.cfg(ds, pp, ph)
        nxt = None if nd is None else fam.cfg(nd, npp, nph)
        if cfg is None or nxt is None:
            continue
        want = cfg_cells(nxt)
        pred, armname = None, None
        for arm in order:
            if rep.apply_rule(arm.rule, cfg, bulk=False) is None:
                continue
            armname = arm.name
            mm = match_rule(arm.rule, cfg)
            s = arm.steps(dict(mm[0]) if mm else {})
            pred = s.c if s.is_const() else None
            break
        q, h, L, R = cfg
        Lc, Rc = list(runs_cells(L)), list(runs_cells(R))
        at, idx, n = None, None, 0
        for t, cq, pos, tape, lo, hi in raw_run(tm, q, h, Lc, Rc, max_steps):
            if t == 0 or cq != fam.q or tape.get(pos, 0) != fam.h:
                continue
            # the anchor_visit_index scan: the head crosses the anchor cell
            # several times per increment, so count the visits and report
            # WHICH one is the successor rather than requiring the first
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            if (cq, fam.h, tuple(gl), tuple(gr)) == want:
                at, idx = t, n
                break
            n += 1
            if n >= max_visits:
                break
        out.append({'v': v, 'k': len(ds), 'to_k': len(nd), 'p': pp,
                    'to_p': npp, 'phase': ph, 'to_phase': nph,
                    'at_fill': all(d == fam.b - 1 for d in ds),
                    'arm': armname, 'shape_ok': at is not None,
                    'anchor_visit_index': idx,
                    'raw_steps': at, 'predicted_steps': pred,
                    'steps_ok': pred is not None and pred == at})
    return out


def chain_check(tm, fam, boot_t, boot_ds, boot_p=None, laps=40,
                max_steps=400000, boot_ph=0):
    """Replay the raw machine from BLANK and confirm the family's successive
    members appear, in order, at the boot offset -- the end-to-end check."""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    ds, pp = list(boot_ds), fam.p0 if boot_p is None else boot_p
    ph = boot_ph
    seen, t = 0, 0
    while t < max_steps and seen <= laps:
        if t >= boot_t and q == fam.q and tape.get(pos, 0) == fam.h:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            cf = fam.cfg(ds, pp, ph)
            want = None if cf is None else cfg_cells(cf)
            if want is not None and (q, fam.h, tuple(gl), tuple(gr)) == want:
                seen += 1
                ds, pp, ph = succ(fam, ds, pp, ph)
                if ds is None:
                    return {'laps_confirmed': seen, 'fill_law_ran_out': True}
        h = tape.get(pos, 0)
        tr = tm.get((q, h))
        if tr is None:
            return {'laps_confirmed': seen, 'halted': True}
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        lo, hi, q, t = min(lo, pos), max(hi, pos), q2, t + 1
    return {'laps_confirmed': seen - 1, 'halted': False}


# --------------------------------------------------------------------- drive

def close(spec, steps=20000, cap=240.0, kmax=7, verbose=False,
          numeration=False):
    t0 = time.time()
    _WALKS.clear()
    _COVERS.clear()
    tm = parse_tm(spec)
    ns = n_states(tm)
    res = {'spec': spec, 'closed': False}
    snaps = simulate(tm, steps)
    if snaps and snaps[-1][1] is None:
        res['reason'] = 'halts'
        return res
    from discover import mine_shapes, build_ladder
    from validate import check_ladder
    table = mine_shapes(snaps)
    rules = build_ladder(tm, table, time_cap=max(20.0, cap * 0.35))
    res['ladder'] = [{'name': r.name, 'lhs': cfg_repr(r.lhs),
                      'rhs': cfg_repr(r.rhs), 'lbs': dict(r.lbs),
                      'dec': r.dec,
                      'fired': {'%s%d' % (chr(65 + t[0]), t[1]): repr(e)
                                for t, e in sorted(r.fired.items())}}
                     for r in rules]
    res['n_rules'] = len(rules)
    bad = check_ladder(tm, rules)
    res['ladder_invalid'] = bad
    if bad:
        res['reason'] = 'ladder rules failed differential validation'
        return res
    if not rules:
        res['reason'] = 'no local rules'
        return res
    fams = find_families(tm, snaps, rules, numeration=numeration)
    res['n_families'] = len(fams)
    if not fams:
        res['family_probe'] = probe_families(tm, snaps, rules)
        res['reason'] = ('no value family: no anchor whose counter side '
                         'decodes over ladder-named digits with +1 steps')
        return res
    # Candidates: every family ONE-parameter first -- that is the behaviour
    # measured at 3341a3c and it must not move -- then, for the families whose
    # far side actually moves, the same family again with the far side
    # generalized to a run template E(p, v).  The two-parameter variant is
    # strictly a fallback, so a row that closes today closes today's way.
    import copy
    cands = [(f, ft, ch, f.otmpl is not None) for f, ft, ch in fams[:4]]
    n_one = len(cands)
    for f, ft, ch in fams[:3]:
        if len(cands) >= 6 or f.otmpl is not None:
            continue
        g = copy.deepcopy(f)
        occ = [(t, sn) for t, sn in snaps if sn is not None
               and (sn[0], sn[1]) == (g.q, g.h)][-400:]
        if fit_far(g, occ):
            cands.append((g, ft, ch, True))
    ntry = len(cands)
    for fi, (fam, ft, chain, two_param) in enumerate(cands):
        if time.time() - t0 > cap:
            res['reason'] = 'time cap'
            return res
        # Budget, not mathematics: the FALLBACK candidates (two-parameter far
        # side, and any candidate past the first few) are what a row that
        # never closes spends its last minute on, and that minute is what
        # pushes a row from `returns a diagnosis` to `hard timeout`.  A
        # fallback only starts if a real slice is left for it.
        if fi >= n_one and time.time() - t0 > 0.7 * cap:
            res['fallback_candidates_skipped'] = ntry - fi
            break
        # Per-family slice, so one hopeless candidate cannot eat the budget.
        # The one-parameter candidates divide the budget among THEMSELVES, so
        # adding two-parameter fallbacks cannot shorten a slice that a row
        # already closes inside; the fallbacks live on what is left.
        den = max(1, (n_one - fi) if fi < n_one else (ntry - fi))
        slice_end = min(t0 + cap,
                        time.time() + max(20.0, (t0 + cap - time.time())
                                          / den))
        ctr = itertools.count()
        # The boot and the FILL LAW come first: the law decides what the
        # successor of a top string is, and the sample the arms are mined from
        # has to contain the fills it predicts.
        # The boot, the fill law and the arms are all read against whichever
        # shape this candidate is -- the far side's template is already fixed
        # by the time we get here, so p widens which visits count as anchors
        # from the start rather than being fixed up afterwards.
        # One raw walk feeds all three: the PHASES (which terminators the
        # machine runs the alphabet through), the fill law of each phase, and
        # the boot.  The phase pass leaves a family that reads all its own
        # anchor visits exactly as it is, so a row that closes today is
        # untouched by it.
        walk = anchor_cells(fam, tm)
        multiphase = fit_phases(fam, walk)
        fill_obs = observe_fill(fam, walk)
        if fam.fills is None:
            fam.fills = fit_fills(fam, fill_obs) or [fam_fill(fam, 0)]
        bt, bds, bp, bph = find_boot(fam, snaps)
        # A fill whose outer-parameter law DECREASES p is not a family any
        # liveness argument can use.  `far_cells` returns None as soon as a
        # count goes negative, so the successor chain is finite BY
        # CONSTRUCTION, and `chain_check`'s 40 laps then say only that 40 is
        # less than p at the boot.  Two of the fifteen read exactly this way
        # once the unary constructor lets them read at all -- a bouncer eating
        # a fixed spacer, `p' = p - 1` -- and the reading is true over the
        # window and false forever, which is the one thing a certificate
        # candidate must never be.  No row that closes today has a fill that
        # moves the outer parameter at all, so this refuses nothing that was
        # already being reported.
        if any(f.moves_p() and f.apply_p(fam.p0, k) < fam.p0
               for f in fam.fills for k in (1, 8)):
            res.setdefault('tried', []).append(
                {'family': fam.json(), 'fill': fam.fill.json(),
                 'reason': 'the fill DECREASES the outer parameter, so the '
                           'family is finite: it is a reading of the window, '
                           'not of the machine'})
            continue
        fill_fitted = all(f.seen for f in fam.fills)
        groups = _groups(fam, (1, 2, 3, 4, 5))
        arms = mine_arms(tm, rules, fam, deadline=slice_end, ctr=ctr,
                         groups=groups)
        if not arms:
            res.setdefault('tried', []).append(
                {'family': fam.json(), 'fill': fam.fill.json(),
                 'reason': 'no arm replayed to anchor'})
            continue
        km = min(kmax, kmax_for(fam.b))
        km2 = km + (2 if fam.b == 2 else 1)
        if fam.weights is not None:
            # A position no equation pinned is not a reading: the family is
            # stated only as wide as the weights were actually fitted, and
            # `Fam.value` returns None past that rather than guessing.
            km2 = min(km2, len(fam.weights))
            km = min(km, max(1, km2 - 2))
        # Enumeration: every digit string first (the strongest claim), and if
        # that fails, the states actually REACHABLE from the boot.  A fill law
        # that widens by more than one puts half the widths out of reach, and
        # asking for arms there asks for configurations the run never enters.
        enum, ok, covmap, rep, rounds = 'all digit strings', False, {}, {}, 0
        # A step other than +1 means only part of each width is a member, so
        # "every digit string" is not a claim the family can make -- those go
        # straight to the states the boot actually reaches.
        modes = ('all', 'reachable') if fam.step == 1 else ('reachable',)
        for mode in modes:
            states = (None if mode == 'all'
                      else reach(fam, bds, bp, km, boot_ph=bph))
            if mode == 'reachable' and (bds is None or len(states or ()) < 8):
                if not rep:
                    res.setdefault('tried', []).append(
                        {'family': fam.json(),
                         'reason': ('no boot into the family' if bds is None
                                    else 'reachable set too short to check')})
                break
            ok, covmap, rep = cover(tm, fam, arms, kmax=km, states=states)
            rounds = 0
            # The repair used to be skipped outright when every failure sat at
            # the overflow -- correctly, while the fill law was hard-coded: no
            # amount of specializing reaches a successor the model has wrong.
            # With the law inferred the fill is an ordinary base case, and
            # these rows are routinely ONE string short of closing.
            while not ok and rounds < 5 and time.time() < slice_end:
                new = repair(tm, rules, fam, arms,
                             rep['uncovered_all'] + rep['wrong_all'], ctr,
                             groups, deadline=slice_end, max_new=32)
                if not new:
                    # nothing new to add: the remaining failures may be an arm
                    # SHADOWING its own repair, so drop the offender and let
                    # the next round rebuild what it was covering
                    trial = drop_wrong(tm, fam, arms, km, states)
                    if len(trial) == len(arms):
                        break
                    arms = trial
                else:
                    arms += new
                ok, covmap, rep = cover(tm, fam, arms, kmax=km, states=states)
                rounds += 1
            rep['repair_rounds'] = rounds
            if ok:
                enum = ('all digit strings' if mode == 'all'
                        else 'states reachable from the boot')
                break
        states = (None if enum == 'all digit strings' and fam.step == 1
                  else reach(fam, bds, bp, km, boot_ph=bph))
        arms = minimize(arms, covmap)
        if ok and time.time() < slice_end:
            arms = prune(tm, fam, arms, km, states, deadline=slice_end)
            ok, covmap, rep2b = cover(tm, fam, arms, km, states)
            rep2b['repair_rounds'] = rounds
            rep = rep2b
        if not ok:
            if not rep:                    # the mode loop never ran a cover
                continue
            res.setdefault('tried', []).append(
                {'family': fam.json(), 'fill': fam.fill.json(),
                 'reason': ('overflow leaves the family'
                            if rep.get('fails_only_at_overflow')
                            else 'family not covered'),
                 'coverage': {k: v for k, v in rep.items()
                              if k not in ('uncovered_all', 'wrong_all')}})
            continue
        # Stability: the same arm set must still cover the next octaves out.
        # A miss here is usually a carry class that only first APPEARS at that
        # width, so give the repair a few rounds at the wider level before
        # calling the family unstable.
        states2 = (None if enum == 'all digit strings'
                   else reach(fam, bds, bp, km2, boot_ph=bph))
        ok2, cov2, rep2 = cover(tm, fam, arms, kmax=km2, states=states2)
        for _ in range(4):
            if ok2 or time.time() > slice_end:
                break
            new = repair(tm, rules, fam, arms,
                         rep2['uncovered_all'] + rep2['wrong_all'], ctr,
                         groups, deadline=slice_end, max_new=32)
            if not new:
                break
            arms += new
            ok2, cov2, rep2 = cover(tm, fam, arms, kmax=km2, states=states2)
        if ok2 and time.time() < slice_end:
            arms = prune(tm, fam, arms, km2, states2, deadline=slice_end)
            ok2, cov2, rep2 = cover(tm, fam, arms, kmax=km2, states=states2)
            rep2['repair_rounds'] = rounds
            rep = {k: v for k, v in rep2.items()
                   if k not in ('uncovered_all', 'wrong_all')}
        rep['stable_to_kmax'] = km2 if ok2 else None
        if not ok2:
            res.setdefault('tried', []).append(
                {'family': fam.json(),
                 'reason': 'coverage not stable at kmax+2',
                 'coverage': {k: v for k, v in rep2.items()
                              if k not in ('uncovered_all', 'wrong_all')}})
            continue
        rep.pop('uncovered_all', None)
        rep.pop('wrong_all', None)
        arms = order_arms(arms)
        if bt is None:
            res.setdefault('tried', []).append(
                {'family': fam.json(), 'fill': fam.fill.json(),
                 'reason': 'no boot into the family'})
            continue
        # Liveness may only read arms taken INFINITELY OFTEN.  An arm still
        # claiming digit strings at the WIDEST width covered claims one at
        # every width it can reach (the run visits every value, so every
        # reachable width recurs); an arm whose last claim is at some fixed
        # width -- the small-k overflow base cases -- fires finitely often and
        # must NOT count.  The widest width is read off the coverage rather
        # than assumed to be km2: a fill that widens by two only ever reaches
        # one parity class.
        top_k = max((k for s in cov2.values() for k, *_ in s), default=km2)
        live, fin = [], []
        for a in arms:
            ks = {k for k, *_ in cov2.get(a.name, ())}
            (live if ks and max(ks) == top_k else fin).append(a)
        fired = {}
        for a in live:
            for tr, e in a.rule.fired.items():
                fired[tr] = fired.get(tr, Expr(0)) + e
        io = {t[0] for t in fired}
        seen = visited_states(tm, bt) | {t[0] for a in arms
                                         for t in a.rule.fired}
        io_letters = sorted(chr(65 + q) for q in io)
        diff = differential(tm, fam, arms, bds, bp, boot_ph=bph)
        chk = chain_check(tm, fam, bt, bds, bp, boot_ph=bph)
        res.update({
            'closed': bool(diff) and all(d['shape_ok'] for d in diff),
            'family': fam.json(),
            'fill': fam.fill.json(),
            'fill_by_phase': [f.json() for f in fam.fills],
            'fill_observed': [[ph, k, ph2, t, pa, pb]
                              for ph, k, ph2, t, pa, pb in fill_obs],
            'fill_law_inferred': fill_fitted,
            'phases': {
                'n': len(fam.tails),
                'terminators': [list(t) for t in fam.tails],
                'found_by_the_phase_pass': multiphase,
                'cycle': ['phase %d top -> phase %d, p+%d'
                          % (i, f.to, f.s) for i, f in enumerate(fam.fills)]},
            'enumeration': enum,
            'two_parameter': two_param,
            'outer_parameter': (None if fam.otmpl is None else {
                'far_side_template': ['%s^(%d*p+%d)' % (''.join(map(str, w)),
                                                        a, b)
                                      for w, a, b in fam.otmpl],
                'p_observed_range': list(fam.prange),
                'p_at_boot': bp,
                'checked_at_p': fam.psample()}),
            'family_first_seen': ft, 'anchor_chain': chain,
            'arms': [a.json() for a in arms],
            'arm_selection': ('first applicable in the order listed; the '
                              'order is a linearization of pattern '
                              'subsumption, most specific first'),
            'arm_order_is_subsumption_linearization': order_ok(arms),
            'arm_selection_shadowed': rep.get('shadowed_by_selection', 0),
            'arms_infinitely_often': [a.name for a in live],
            'arms_finitely_often': [a.name for a in fin],
            'coverage': rep,
            'boot': {'steps_from_blank': bt, 'digits_lsb_first': bds,
                     'value': fam.value(bds), 'p': bp, 'phase': bph,
                     'cells': fam.encode(bds, bph, bp)},
            'liveness': {
                'fired_transitions': sorted('%s%d' % (chr(65 + t[0]), t[1])
                                            for t in fired),
                'states_infinitely_often': ''.join(io_letters),
                'states_visited': ''.join(sorted(chr(65 + q) for q in seen)),
                'read_from_arms': [a.name for a in live],
                'all_states': len(io) == ns,
                'never_quasihalts': seen <= io,
                'quasihalts_at_states': ''.join(
                    sorted(chr(65 + q) for q in seen - io))},
            'differential': diff,
            'differential_ok': all(d['shape_ok'] for d in diff),
            'differential_steps_ok': all(d['steps_ok'] for d in diff),
            'chain_check': chk,
            'seconds': round(time.time() - t0, 1)})
        if not res['closed']:
            res['reason'] = ('differential mismatch: the family closes but '
                             'the raw simulator disagrees -- engine bug')
        return res
    res['reason'] = res.get('reason', 'families found but none closed')
    res.setdefault('family_probe', probe_families(tm, snaps, rules))
    res['seconds'] = round(time.time() - t0, 1)
    return res


def main():
    import argparse
    import sys
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--list')
    ap.add_argument('--steps', type=int, default=20000)
    ap.add_argument('--cap', type=float, default=240.0)
    ap.add_argument('--kmax', type=int, default=7)
    ap.add_argument('--json')
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--numeration', action='store_true',
                    help='also run the NUMERATION pass when the main pass '
                         'found only floor-chain families (LADDER_PLAN 4s)')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.split()[0] for l in open(a.list) if l.strip()]
    out = []
    for spec in specs:
        r = close(spec, a.steps, a.cap, a.kmax, a.verbose,
                  numeration=a.numeration)
        out.append(r)
        print('%-30s %s' % (spec, {
            'closed': r['closed'], 'rules': r.get('n_rules'),
            'arms': len(r.get('arms', [])),
            'live': r.get('liveness', {}).get('states_infinitely_often'),
            'diff': r.get('differential_ok'),
            'steps_ok': r.get('differential_steps_ok'),
            'laps': r.get('chain_check', {}).get('laps_confirmed'),
            'sec': r.get('seconds'),
            'reason': r.get('reason')}))
        sys.stdout.flush()
        if a.verbose and r['closed']:
            print(json.dumps(r, indent=1)[:6000])
    if a.json:
        with open(a.json, 'w') as f:
            for r in out:
                f.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    main()
