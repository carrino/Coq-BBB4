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


# ------------------------------------------------------------------- family

class Fam:
    """CTR(alph, v): counter segment on `side`, digits nearest-first with the
    LEAST significant digit adjacent to the head."""

    def __init__(self, q, h, side, other, digs, pre, named_by, tail=()):
        self.q, self.h, self.side = q, h, side
        self.other = tuple(other)
        self.digs = [tuple(d) for d in digs]
        self.pre = tuple(pre)
        self.tail = tuple(tail)     # fixed terminator at the far end
        self.named_by = named_by          # digit word -> ladder rule name
        self.l = len(self.digs[0])
        self.b = len(self.digs)
        self.idx = {d: i for i, d in enumerate(self.digs)}
        self.fill = None                  # the width law, inferred later

    def key(self):
        return (self.q, self.h, self.side, self.other, tuple(self.digs),
                self.pre, self.tail)

    def decode(self, cells):
        """cells (nearest-first, trailing blanks stripped) -> digits LSB-first.
        Blanks stripped off the far end are restored by the pad loop."""
        base = list(cells)
        if tuple(base[:len(self.pre)]) != self.pre:
            return None
        for pad in range(self.l + len(self.tail) + 1):
            c = base + [0] * pad
            n = len(c) - len(self.pre) - len(self.tail)
            if n < 0 or n % self.l:
                continue
            if self.tail and tuple(c[len(c) - len(self.tail):]) != self.tail:
                continue
            mid = c[len(self.pre):len(self.pre) + n]
            ds, ok = [], True
            for i in range(0, n, self.l):
                g = tuple(mid[i:i + self.l])
                if g not in self.idx:
                    ok = False
                    break
                ds.append(self.idx[g])
            if ok and self.encode(ds) == list(cells):
                return ds
        return None

    def encode(self, ds):
        cells = list(self.pre)
        for d in ds:
            cells.extend(self.digs[d])
        cells.extend(self.tail)
        while cells and cells[-1] == 0:
            cells.pop()
        return cells

    def value(self, ds):
        v = 0
        for d in reversed(ds):
            v = v * self.b + d
        return v

    def cfg(self, ds):
        """The counter segment in ITS OWN alphabet -- one run per maximal
        stretch of equal digits -- NOT in the miner's greedy block RLE.  This
        is the whole point of CTR being a tape item: under greedy blocking the
        run words near the head depend on digits arbitrarily far away (a
        period-3 bit pattern invents a 6-cell block word), so no bounded set of
        local shapes covers the family.  Digit-aligned, the run vocabulary is
        the alphabet itself and the near-head runs are a function of the
        near-head digits -- which is what makes the arms LOCAL."""
        runs = [((c,), Expr(1)) for c in self.pre]
        i = 0
        while i < len(ds):
            k = i
            while k < len(ds) and ds[k] == ds[i]:
                k += 1
            runs.append(canon_run(self.digs[ds[i]], Expr(k - i)))
            i = k
        runs.extend(((c,), Expr(1)) for c in self.tail)
        out = []
        for w, e in runs:
            if out and out[-1][0] == w:
                out[-1] = (w, out[-1][1] + e)
            else:
                out.append((w, e))
        while out and set(out[-1][0]) == {0}:
            out.pop()
        c = tuple(out)
        o = block_rle(list(self.other))
        return (self.q, self.h, c, o) if self.side == 'L' else \
               (self.q, self.h, o, c)

    def counter_side(self, cfg):
        return cfg[2] if self.side == 'L' else cfg[3]

    def other_side(self, cfg):
        return cfg[3] if self.side == 'L' else cfg[2]

    def anchor_shaped(self, cfg):
        if (cfg[0], cfg[1]) != (self.q, self.h):
            return False
        oc = runs_cells(self.other_side(cfg))
        return oc is not None and tuple(oc) == self.other

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

    def aligned(self, cells):
        """Is this a digit-aligned PREFIX of some family member?  The wall
        marker hides the rest, so a local arm's landing config can only be
        checked this far -- but this far is enough to catch a stop that is
        mid-digit, which is what landing off the family looks like."""
        n = min(len(cells), len(self.pre))
        if tuple(cells[:n]) != self.pre[:n]:
            return False
        mid = cells[len(self.pre):]
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
        return self.aligned(cells) if mk else self.decode(cells) is not None

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
                'terminator': list(self.tail),
                'base': self.b, 'digit_len': self.l,
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
    width level; the arms below it are unchanged."""

    __slots__ = ('s', 'pre', 'mid', 'suf', 'seen')

    def __init__(self, s, pre=(), mid=0, suf=(), seen=()):
        self.s, self.mid = s, mid
        self.pre, self.suf = tuple(pre), tuple(suf)
        self.seen = tuple(seen)

    def apply(self, k):
        n = k + self.s - len(self.pre) - len(self.suf)
        if n < 0:
            return None
        return list(self.pre) + [self.mid] * n + list(self.suf)

    def is_carry(self):
        return (self.s, self.pre, self.mid, self.suf) == (1, (), 0, (1,))

    def json(self):
        return {'widens_by': self.s, 'target_prefix': list(self.pre),
                'target_fill_digit': self.mid, 'target_suffix': list(self.suf),
                'law': 'E(p, b^p - 1) -> E(p+%d, %s)'
                       % (self.s, ''.join(map(str, self.pre)) + '<%d>' % self.mid
                          + ''.join(map(str, self.suf))),
                'inferred_from_widths': list(self.seen),
                'is_the_odometer_carry': self.is_carry()}


CARRY = Fill(1, (), 0, (1,))


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


def next_ds(fam, ds):
    """Odometer successor inside a width; the family's FILL LAW at the top."""
    ds = list(ds)
    i = 0
    while i < len(ds) and ds[i] == fam.b - 1:
        ds[i] = 0
        i += 1
    if i == len(ds):
        return (fam.fill or CARRY).apply(len(ds))
    ds[i] += 1
    return ds


def observe_fill(fam, snaps, want=6):
    """Read the fill law off the anchor visits: every time the machine is at
    the top string of some width, record where the NEXT family member is."""
    seq = []
    for t, s in snaps:
        if s is None:
            break
        if not fam.anchor_shaped(s):
            continue
        c = runs_cells(fam.counter_side(s))
        if c is None:
            continue
        seq.append(fam.decode(c))
    obs, seen = [], set()
    for a, b in zip(seq, seq[1:]):
        if not a or b is None:
            continue
        k = len(a)
        if any(d != fam.b - 1 for d in a) or k in seen:
            continue
        seen.add(k)
        obs.append((k, b))
        if len(obs) >= want:
            break
    return obs


def trailing_max(fam, ds):
    j = 0
    while j < len(ds) and ds[j] == fam.b - 1:
        j += 1
    return j


# ----------------------------------------------------------------- discovery

def find_families(tm, snaps, rules, max_anchor=8, min_chain=8, max_occ=200,
                  max_other=3):
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
            for other, n in pop.most_common(max_other):
                if n < min_chain:
                    break
                sel = [i for i in range(len(occ)) if os[i] == other]
                suf = _common_suffix([cs[i] for i in sel if cs[i]])
                for l in lens:
                    for tl in range(min(len(suf), 2 * l) + 1):
                        tail = tuple(suf[len(suf) - tl:]) if tl else ()
                        for p in range(l):
                            fam = _try_parse(q, h, side, other, occ, cs, sel,
                                             l, p, tail, seeds, min_chain)
                            if fam is not None and fam[0].key() not in seen:
                                seen.add(fam[0].key())
                                found.append(fam)
    # longest +1 chain first; ties to the cleanest reading (shortest
    # terminator, no near-head prefix, narrowest digit)
    found.sort(key=lambda f: (-f[2], len(f[0].tail), len(f[0].pre), f[0].l))
    return found


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


def _grams(cs, sel, l, p, tail):
    grams, pres = [], []
    for i in sel:
        c = cs[i]
        if c is None or len(c) < p + len(tail):
            grams.append(None)
            pres.append(None)
            continue
        pres.append(tuple(c[:p]))
        mid = None
        for pad in range(l + len(tail) + 1):
            cc = list(c) + [0] * pad
            n = len(cc) - p - len(tail)
            if n < 0 or n % l:
                continue
            if tail and tuple(cc[len(cc) - len(tail):]) != tail:
                continue
            mid = cc[p:p + n]
            break
        if mid is None:
            grams.append(None)
            continue
        grams.append(tuple(tuple(mid[j:j + l]) for j in range(0, len(mid), l)))
    return grams, pres


def _try_parse(q, h, side, other, occ, cs, sel, l, p, tail, seeds, min_chain):
    grams, pres = _grams(cs, sel, l, p, tail)
    alpha = set()
    for g in grams:
        if g:
            alpha |= set(g)
    if not (2 <= len(alpha) <= 3):
        return None
    # accept either a digit word the ladder names outright, or a digit WIDTH
    # the ladder names -- the latter only on a chain twice as long, since the
    # +1 evidence is then carrying the whole alphabet claim
    strong = any(a in seeds for a in alpha)
    need = min_chain if strong else 2 * min_chain
    best = None
    for perm in itertools.permutations(sorted(alpha)):
        idx = {a: i for i, a in enumerate(perm)}
        vals = []
        for g, pr in zip(grams, pres):
            if g is None or pr is None or any(x not in idx for x in g):
                vals.append(None)
                continue
            v = 0
            for x in reversed(g):
                v = v * len(perm) + idx[x]
            vals.append((v, pr))
        i = 0
        while i < len(vals):
            if vals[i] is None:
                i += 1
                continue
            k = i
            while (k + 1 < len(vals) and vals[k + 1] is not None
                   and vals[k + 1][1] == vals[i][1]
                   and vals[k + 1][0] == vals[k][0] + 1):
                k += 1
            if k - i + 1 >= need and (best is None or k - i + 1 > best[2]):
                nm = {a: seeds[a] for a in perm if a in seeds}
                best = (Fam(q, h, side, other, list(perm), vals[i][1], nm,
                            tail), occ[sel[i]][0], k - i + 1)
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

class Arm:
    def __init__(self, name, rule, ops, kind, uses):
        self.name, self.rule, self.ops = name, rule, ops
        self.kind, self.uses = kind, uses
        self.covers = []

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
    out = []
    for k in range(1, kmax + 1):
        for v in range(fam.b ** k):
            ds = []
            x = v
            for _ in range(k):
                ds.append(x % fam.b)
                x //= fam.b
            out.append(ds)
    for k in extra:
        for seed in (0, 1, 2):
            ds = [(i * 7 + seed * 3 + k) % fam.b for i in range(k)]
            out.append(ds)
    # the TOP string at every width, and where the fill law sends it.  The
    # fill arm is generalized across these, so they have to be in the sample
    # at more widths than the exhaustive part reaches -- one instance is a
    # base case, several are an induction.
    for k in range(1, 13):
        out.append([fam.b - 1] * k)
        t = (fam.fill or CARRY).apply(k)
        if t:
            out.append(t)
    return out


def _vkey(v):
    return (v[0], v[1], tuple(w for w, _ in v[2]), tuple(w for w, _ in v[3]))


def _groups(fam, windows, max_exact_runs=4):
    """key -> [(ds, view)] over the sampled digit strings."""
    g = defaultdict(list)
    for ds in sample_digits(fam):
        cfg = fam.cfg(ds)
        for m in windows:
            v = fam.view(cfg, m)
            g[_vkey(v)].append((ds, v))
        if len(fam.counter_side(cfg)) <= max_exact_runs:
            v = fam.view(cfg, 0, marker=False)   # exact: the overflow arm
            g[_vkey(v)].append((ds, v))
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
        for arm in _replay_arm(tm, rules, fam, lhs, lbs, next(ctr), budget):
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
    for k, v in uncovered:
        if len(added) >= max_new or (deadline and time.time() > deadline):
            break
        ds, x = [], v
        for _ in range(k):
            ds.append(x % fam.b)
            x //= fam.b
        cfg = fam.cfg(ds)
        want = cfg_cells(fam.cfg(next_ds(fam, ds)))
        first = None
        for a in sorted(arms + added, key=spec_key):
            if rep.apply_rule(a.rule, cfg, bulk=False) is not None:
                first = a
                break
        if first is not None and \
                cfg_cells(rep.apply_rule(first.rule, cfg, bulk=False)) == want:
            continue
        got = None
        for m in windows:
            for mk in (True, False):
                view = fam.view(cfg, m, marker=mk)
                key = _vkey(view)
                cs = [e.c for e in cfg_counts(view)]
                for T in pins:
                    pin = {i for i, c in enumerate(cs) if c <= T}
                    insts = [(d, w) for d, w in groups.get(key, [])
                             if all(cfg_counts(w)[i].c == cs[i] for i in pin)]
                    lhs, lbs = _generalize(insts + [(ds, view)], pin)
                    if lhs is None:
                        continue
                    # try EVERY anchor stop the replay offers, not just the
                    # first: past a fill the family member is several anchor
                    # visits along, and taking the first stop is exactly how
                    # an arm lands off the family.
                    for arm in _replay_arm(tm, rules, fam, lhs, lbs,
                                           next(ctr), budget):
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


def _replay_arm(tm, rules, fam, lhs, lbs, idx, budget, max_stops=6):
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
    """Specificity: an arm pinning the whole side (it can see the counter END)
    outranks a local one; within a class the MOST GENERAL goes first -- less
    context, more free variables -- so the symbolic arms own the bulk and the
    pinned base cases only pick up what the lower bounds leave.  The family's
    case split is FIRST APPLICABLE IN THIS ORDER -- it has to be a function,
    because several proved arms can apply to one config and stop at DIFFERENT
    anchors along the same trajectory (an interior arm firing at an overflow
    lands a whole carry short).  Deterministic order, one arm per value."""
    q, h, L, R = arm.rule.lhs
    runs = L + R
    local = any(w == MARKER for w, _ in runs)
    nv = len({v for e in cfg_counts(arm.rule.lhs) for v in e.v})
    return (1 if local else 0, len(runs), -nv, arm.name)


def only_at_overflow(fam, strings):
    """Are these digit strings exactly the all-max ones -- the fill?"""
    return bool(strings) and all(v == fam.b ** k - 1 for k, v in strings)


def all_strings(fam, kmax):
    out = []
    for k in range(1, kmax + 1):
        for v in range(fam.b ** k):
            ds, x = [], v
            for _ in range(k):
                ds.append(x % fam.b)
                x //= fam.b
            out.append(ds)
    return out


def reach(fam, boot_ds, kmax, cap=4000):
    """The states the machine actually VISITS: walk the successor from the
    boot.  With a fill law that widens by more than one, the widths reachable
    from the boot are one parity class -- and demanding coverage of the other
    parity demands arms for configurations the run never enters.  (That is the
    `..._at_octave_parity_0` gate label, read from this side.)"""
    out, seen, ds = [], set(), list(boot_ds)
    while ds is not None and len(ds) <= kmax and len(out) < cap:
        key = (len(ds), fam.value(ds))
        if key in seen:
            break
        seen.add(key)
        out.append(list(ds))
        ds = next_ds(fam, ds)
    return out


def cover(tm, fam, arms, kmax=7, states=None):
    """Every digit string in `states` (default: all up to kmax digits): the
    FIRST applicable arm (by spec_key) must land on the successor.  Returns
    (ok, covmap, report)."""
    rep = Replay(tm, [], budget=4, raise_ok=False)
    arms = sorted(arms, key=spec_key)
    uncovered, wrong, used = [], [], defaultdict(int)
    covmap = defaultdict(set)
    total = 0
    for ds in (all_strings(fam, kmax) if states is None else states):
        nd = next_ds(fam, ds)
        if nd is None:
            continue
        k, v = len(ds), fam.value(ds)
        total += 1
        cfg = fam.cfg(ds)
        want = cfg_cells(fam.cfg(nd))
        hit = 0
        for arm in arms:
            out = rep.apply_rule(arm.rule, cfg, bulk=False)
            if out is None:
                continue
            if cfg_cells(out) != want:
                wrong.append((arm.name, k, v))
                break
            hit += 1
            used[arm.name] += 1
            covmap[arm.name].add((k, v))
            if len(arm.covers) < 8:
                arm.covers.append(v)
            break
        if hit == 0 and (not wrong or wrong[-1][1:] != (k, v)):
            uncovered.append((k, v))
    ok = not uncovered and not wrong
    return ok, covmap, {'strings': total, 'kmax': kmax,
                'uncovered': uncovered[:12], 'n_uncovered': len(uncovered),
                'uncovered_all': uncovered,
                'wrong': wrong[:12], 'n_wrong': len(wrong),
                'wrong_all': [(k, v) for _, k, v in wrong],
                'wrong_only_at_overflow': only_at_overflow(
                    fam, [(k, v) for _, k, v in wrong]),
                'fails_only_at_overflow': only_at_overflow(
                    fam, uncovered + [(k, v) for _, k, v in wrong]),
                'arm_hits': dict(used)}


def prune(tm, fam, arms, kmax, states=None):
    """Drop any arm the family still covers correctly without: the window
    sweep leaves whole-side variants of arms whose local form already does
    the job.  Least-used first, one re-check per drop."""
    ok, covmap, _ = cover(tm, fam, arms, kmax, states)
    if not ok:
        return arms
    for a in sorted(arms, key=lambda a: len(covmap.get(a.name, ()))):
        if len(arms) == 1:
            break
        trial = [x for x in arms if x is not a]
        ok2, cov2, _ = cover(tm, fam, trial, kmax, states)
        if ok2:
            arms, covmap = trial, cov2
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
    """First trace index whose config IS a family member."""
    for t, s in snaps:
        if s is None:
            break
        if not fam.anchor_shaped(s):
            continue
        c = runs_cells(fam.counter_side(s))
        if c is None:
            continue
        ds = fam.decode(c)
        if not ds:
            continue
        if cfg_cells(fam.cfg(ds)) != cfg_cells(s):
            continue
        return t, ds
    return None, None


# ------------------------------------------------------- differential checks

def differential(tm, fam, arms, boot_ds, n_checks=18, max_steps=400000,
                 max_visits=24):
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
    walk = reach(fam, boot_ds, kmax=9, cap=6000)
    tops = [i for i, ds in enumerate(walk)
            if all(d == fam.b - 1 for d in ds)]
    want_i = set()
    for i in tops:
        want_i |= {i - 1, i, i + 1}
    for i in (0, 1, 2, 5, 11, len(walk) // 2, len(walk) - 2):
        want_i.add(i)
    probes = [walk[i] for i in sorted(want_i)
              if 0 <= i < len(walk)][:n_checks]
    rep = Replay(tm, [], budget=4, raise_ok=False)
    order = sorted(arms, key=spec_key)
    out = []
    for ds in probes:
        v = fam.value(ds)
        nd = next_ds(fam, ds)
        if nd is None:
            continue
        cfg = fam.cfg(ds)
        want = cfg_cells(fam.cfg(nd))
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
        out.append({'v': v, 'k': len(ds), 'to_k': len(nd),
                    'at_fill': all(d == fam.b - 1 for d in ds),
                    'arm': armname, 'shape_ok': at is not None,
                    'anchor_visit_index': idx,
                    'raw_steps': at, 'predicted_steps': pred,
                    'steps_ok': pred is not None and pred == at})
    return out


def chain_check(tm, fam, boot_t, boot_ds, laps=40, max_steps=400000):
    """Replay the raw machine from BLANK and confirm the family's successive
    members appear, in order, at the boot offset -- the end-to-end check."""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    ds = list(boot_ds)
    seen, t = 0, 0
    while t < max_steps and seen <= laps:
        if t >= boot_t and q == fam.q and tape.get(pos, 0) == fam.h:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            want = cfg_cells(fam.cfg(ds))
            if (q, fam.h, tuple(gl), tuple(gr)) == want:
                seen += 1
                ds = next_ds(fam, ds)
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

def close(spec, steps=20000, cap=240.0, kmax=7, verbose=False):
    t0 = time.time()
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
    fams = find_families(tm, snaps, rules)
    res['n_families'] = len(fams)
    if not fams:
        res['family_probe'] = probe_families(tm, snaps, rules)
        res['reason'] = ('no value family: no anchor whose counter side '
                         'decodes over ladder-named digits with +1 steps')
        return res
    ntry = 4
    for fi, (fam, ft, chain) in enumerate(fams[:ntry]):
        if time.time() - t0 > cap:
            res['reason'] = 'time cap'
            return res
        # per-family slice, so one hopeless candidate cannot eat the budget
        slice_end = min(t0 + cap,
                        time.time() + max(20.0, (t0 + cap - time.time())
                                          / max(1, ntry - fi)))
        ctr = itertools.count()
        # The boot and the FILL LAW come first: the law decides what the
        # successor of a top string is, and the sample the arms are mined from
        # has to contain the fills it predicts.
        bt, bds = find_boot(fam, snaps)
        fill_obs = observe_fill(fam, snaps)
        fam.fill = fit_fill(fill_obs) or CARRY
        fill_fitted = fam.fill is not CARRY or bool(fill_obs)
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
        # Enumeration: every digit string first (the strongest claim), and if
        # that fails, the states actually REACHABLE from the boot.  A fill law
        # that widens by more than one puts half the widths out of reach, and
        # asking for arms there asks for configurations the run never enters.
        enum, ok, covmap, rep, rounds = 'all digit strings', False, {}, {}, 0
        for mode in ('all', 'reachable'):
            states = None if mode == 'all' else reach(fam, bds, km)
            if mode == 'reachable' and (bds is None or len(states or ()) < 8):
                break
            ok, covmap, rep = cover(tm, fam, arms, kmax=km, states=states)
            rounds = 0
            while (not ok and rounds < 5 and time.time() < slice_end
                   and not rep['fails_only_at_overflow']):
                new = repair(tm, rules, fam, arms,
                             rep['uncovered_all'] + rep['wrong_all'], ctr,
                             groups, deadline=slice_end, max_new=32)
                if not new:
                    break
                arms += new
                ok, covmap, rep = cover(tm, fam, arms, kmax=km, states=states)
                rounds += 1
            rep['repair_rounds'] = rounds
            if ok:
                enum = ('all digit strings' if mode == 'all'
                        else 'states reachable from the boot')
                break
        states = None if enum == 'all digit strings' else reach(fam, bds, km)
        arms = minimize(arms, covmap)
        if ok and time.time() < slice_end:
            arms = prune(tm, fam, arms, km, states)
            ok, covmap, rep2b = cover(tm, fam, arms, km, states)
            rep2b['repair_rounds'] = rounds
            rep = rep2b
        if not ok:
            res.setdefault('tried', []).append(
                {'family': fam.json(), 'fill': fam.fill.json(),
                 'reason': ('overflow leaves the family'
                            if rep['fails_only_at_overflow']
                            else 'family not covered'),
                 'coverage': {k: v for k, v in rep.items()
                              if k not in ('uncovered_all', 'wrong_all')}})
            continue
        # Stability: the same arm set must still cover the next octaves out.
        # A miss here is usually a carry class that only first APPEARS at that
        # width, so give the repair a few rounds at the wider level before
        # calling the family unstable.
        states2 = None if enum == 'all digit strings' else reach(fam, bds, km2)
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
            arms = prune(tm, fam, arms, km2, states2)
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
        arms = sorted(arms, key=spec_key)
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
        top_k = max((k for s in cov2.values() for k, _ in s), default=km2)
        live, fin = [], []
        for a in arms:
            ks = {k for k, _ in cov2.get(a.name, ())}
            (live if ks and max(ks) == top_k else fin).append(a)
        fired = {}
        for a in live:
            for tr, e in a.rule.fired.items():
                fired[tr] = fired.get(tr, Expr(0)) + e
        io = {t[0] for t in fired}
        seen = visited_states(tm, bt) | {t[0] for a in arms
                                         for t in a.rule.fired}
        io_letters = sorted(chr(65 + q) for q in io)
        diff = differential(tm, fam, arms, bds)
        chk = chain_check(tm, fam, bt, bds)
        res.update({
            'closed': bool(diff) and all(d['shape_ok'] for d in diff),
            'family': fam.json(),
            'fill': fam.fill.json(),
            'fill_observed': [[k, t] for k, t in fill_obs],
            'fill_law_inferred': fill_fitted,
            'enumeration': enum,
            'family_first_seen': ft, 'anchor_chain': chain,
            'arms': [a.json() for a in arms],
            'arm_selection': 'first applicable in the order listed',
            'arms_infinitely_often': [a.name for a in live],
            'arms_finitely_often': [a.name for a in fin],
            'coverage': rep,
            'boot': {'steps_from_blank': bt, 'digits_lsb_first': bds,
                     'value': fam.value(bds),
                     'cells': fam.encode(bds)},
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
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.split()[0] for l in open(a.list) if l.strip()]
    out = []
    for spec in specs:
        r = close(spec, a.steps, a.cap, a.kmax, a.verbose)
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
