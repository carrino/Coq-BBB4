#!/usr/bin/env python3
"""UNTRUSTED measurement: what ARE the `no value family` rows?

`valfam.find_families` reports `no value family: no anchor whose counter side
decodes over ladder-named digits with +1 steps` for fifteen rows of the live
core.  That string records how a SEARCH failed.  This file asks, per row and
per candidate anchor, what the machine is actually doing, varying the four
things the search fixes -- the BASE, the CODE, the STEP and the TERMINATOR --
INDEPENDENTLY rather than in the search's nested order, plus a fifth the search
does not have at all:

    the WEIGHT SEQUENCE.  `Fam.decode` sums d_i * b^i.  That is one numeration
    system out of many, and a machine counting in another (Fibonacci, mixed
    radix, ...) reads as `no +1 chain` against the assumption rather than
    against its own behaviour -- the same error §4e/§4f/§4g made four times
    over the carry, the anchor, the base and the terminator.

Nothing here proves anything and nothing here is a fix.  `valfam.py` is
imported READ-ONLY.

Three passes, cheapest first:

  1. `successor_test` -- IS there a monotone quantity at this anchor at all?
     The question is code-free: a counter is a machine whose next counter-side
     string is a FUNCTION of the current one.  If it is, the rank in that
     chain is a monotone quantity by construction and every numeration
     question is downstream.  If it is not, no (base, code, step, terminator)
     can rescue the anchor and the obstacle is elsewhere.

  2. `readings` -- WHICH numeration.  Strip a terminator (one, or a SET of
     them), fit digit values by permutation, then fit the digit WEIGHTS
     exactly (`fit_weights`: rational Gaussian elimination over the
     within-width rank differences).  Reports `base-b` when the fitted
     weights are b^i, `fibonacci` when they are the Fibonacci sequence,
     `mixed` otherwise -- and also runs the two codes and the three steps, so
     a row the current search could reach with a different terminator alone
     is not miscredited to the weights.  Scored by `order_fit`, which asks
     whether the machine's own first-appearance order inside a width class IS
     the numeration's order; `chain_skip` adds the consecutiveness detail.
     `binomial_probe` measures one numeration that no weight sequence can
     express, and `unary_probe` measures one that needs no digits at all --
     the counter side as a run template `word^p`, where the value IS the run
     count.

  3. `far_class` / `anchor_probe` -- if the counter side is not the obstacle,
     what is?  Far side taxonomy (constant / template / second counter /
     bounded oscillation / unbounded independent), and whether a recurring
     configuration exists that is not a (state, head) visit.

Usage:  nofam.py rows.txt [--json out.jsonl] [--visits N]
"""

import argparse
import collections
import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from engine import parse_tm                                     # noqa: E402
from trace import simulate                                      # noqa: E402
import valfam as V                                              # noqa: E402


FIB = [1, 1]
while len(FIB) < 40:
    FIB.append(FIB[-1] + FIB[-2])


# --------------------------------------------------------------- the walk

def anchors(tm, steps=200000, cap=6000, top=8, min_visits=40):
    """Candidate anchors from the RAW run, busiest first.

    `find_families` takes its anchors from the mining snapshots; the raw walk
    sees more visits and, more to the point, sees them without the mining
    trace's length cap, which is what decides whether a width class is
    complete enough to fit anything on."""
    tape, pos, cq, lo, hi = {}, 0, 0, 0, 0
    cnt = collections.Counter()
    for _ in range(steps):
        cell = tape.get(pos, 0)
        cnt[(cq, cell)] += 1
        tr = tm.get((cq, cell))
        if tr is None:
            break
        w, d, cq = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
    return [qh for qh, n in cnt.most_common(top) if n >= min_visits]


def sides(tm, q, h, steps=200000, cap=6000):
    """(counter cells, far cells) per anchor visit, for both sides."""
    w = V.raw_anchor_visits(tm, q, h, steps, cap)
    L = [tuple(V.runs_cells(a) or ()) for a, _ in w]
    R = [tuple(V.runs_cells(b) or ()) for _, b in w]
    return {'L': (L, R), 'R': (R, L)}


# ------------------------------------------------- pass 1: is it monotone?

def successor_test(ctr):
    """Is the next counter-side string a FUNCTION of the current one?

    Code-free, terminator-free, base-free: this is the question every
    numeration question is downstream of.  Returns the fraction of observed
    strings whose successor is unique, the fraction of consecutive PAIRS that
    obey the majority successor, and the number of distinct strings.

    Consecutive repeats (the head crosses the anchor cell without the counter
    moving) are dropped rather than counted against: `chain_frac` in
    `valfam.py` makes the same allowance and for the same reason."""
    succ = collections.defaultdict(collections.Counter)
    for a, b in zip(ctr, ctr[1:]):
        if a == b:
            continue
        succ[a][b] += 1
    if not succ:
        return None
    uniq = sum(1 for c in succ.values() if len(c) == 1)
    pairs = sum(sum(c.values()) for c in succ.values())
    good = sum(c.most_common(1)[0][1] for c in succ.values())
    return {'distinct': len(set(ctr)),
            'states_with_unique_successor': round(uniq / len(succ), 3),
            'pairs_following_majority': round(good / pairs, 3),
            'n_states': len(succ), 'n_pairs': pairs}


def width_classes(ctr, tail_len=0, top=12):
    """Distinct strings per length after stripping `tail_len` cells off the
    far end -- `numsys.py`'s fingerprint, but computed on the RAW walk and for
    an arbitrary terminator instead of only the constant-far-side group."""
    by = collections.defaultdict(set)
    for c in ctr:
        if len(c) < tail_len:
            continue
        by[len(c) - tail_len].add(c[:len(c) - tail_len] if tail_len else c)
    ks = sorted(by)[:top]
    return [(k, len(by[k])) for k in ks]


def growth_ratio(cls):
    r = [b / a for (k1, a), (k2, b) in zip(cls, cls[1:])
         if a and k2 == k1 + 1]
    if not r:
        return None
    return round(sorted(r)[len(r) // 2], 3)


# --------------------------------------------- pass 2: name the numeration

def suffixes(ctr, maxlen=5, min_frac=0.15, cap=8):
    """Candidate TERMINATORS: every suffix up to `maxlen` shared by at least
    `min_frac` of the visits, plus the empty one.

    `Fam` pins the common suffix of one constant-far-side group.  These rows
    have no such group of any size, so the terminator has to be read off the
    whole walk or not at all."""
    n = len(ctr)
    got = []
    for t in range(1, maxlen + 1):
        c = collections.Counter(x[len(x) - t:] for x in ctr if len(x) >= t)
        for suf, k in c.most_common(3):
            if k >= min_frac * n:
                got.append((k, suf))
    got.sort(key=lambda x: (-x[0], len(x[1])))
    return [()] + [s for _, s in got[:cap]]


def grams_multi(ctr, l, p, tails):
    """Digit tuples under a SET of terminators -- LADDER_PLAN sec.4f's phases,
    but with the terminators varied rather than read off one family.

    A visit is parsed by the longest candidate terminator that fits.  The
    width returned is `(digits, which terminator)` collapsed to one increasing
    integer, so a machine that laps the same alphabet through terminator 0 and
    then terminator 1 before widening reads as two width classes rather than
    as one class visited twice."""
    order = sorted(set(tails), key=lambda t: -len(t))
    out = []
    for c in ctr:
        got = None
        for ti, tail in enumerate(order):
            tl = len(tail)
            if len(c) < p + tl or (tl and c[len(c) - tl:] != tail):
                continue
            mid = c[p:len(c) - tl]
            if len(mid) % l:
                continue
            got = (tuple(tuple(mid[j:j + l]) for j in range(0, len(mid), l)),
                   len(order) - 1 - ti)
            break
        out.append(got)
    return out


def grams(ctr, l, p, tail):
    """Digit tuples per visit, LSB-first, after a `p`-cell near-head prefix
    and a `tail` terminator; None where the string does not parse."""
    tl = len(tail)
    out = []
    for c in ctr:
        if len(c) < p + tl or (tl and c[len(c) - tl:] != tail):
            out.append(None)
            continue
        mid = c[p:len(c) - tl]
        if len(mid) % l:
            out.append(None)
            continue
        out.append(tuple(tuple(mid[j:j + l]) for j in range(0, len(mid), l)))
    return out


def _solve(eqs, W):
    """Exact rational solve of `eqs` = [(coeffs, rhs)] for W unknowns, adding
    equations greedily and COUNTING the ones that contradict what is already
    fixed.  Greedy rather than least-squares on purpose: a handful of
    mid-flight tapes must not drag the fit, they must be counted."""
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


def fit_weights(ds, maxW=14):
    """Fit a WEIGHT per digit position, from the machine's own enumeration
    ORDER rather than from an assumed radix.

    `Fam.decode` sums `d_i * b**i`.  That is one numeration system; the
    question this file exists to ask is which one the machine is in.  Inside a
    width class the strings appear in the order the counter reaches them, so
    the RANK of a string by first appearance is its value if the machine is
    counting at all -- and that is an observation, not an assumption.  Fitting
    `sum d_i w_i = rank` over every width class at once then either produces a
    single weight sequence that explains every class (a positional numeration,
    whatever its radix) or does not.

    Rank rather than consecutive visits because a family MEMBER is a
    subsequence of the anchor visits (LADDER_PLAN sec.4e): consecutive-pair
    equations are half mid-flight on an interleaved row, and a greedy solve
    takes whichever came first.  Returns (weights, violated fraction)."""
    order, seen = collections.defaultdict(list), set()
    for d in ds:
        if d is None or d in seen:
            continue
        seen.add(d)
        order[len(d)].append(d)
    eqs = []
    W = 0
    for n, ss in order.items():
        if len(ss) < 3 or n > maxW:
            continue
        W = max(W, n)
        # DIFFERENCES of consecutive ranks, not the ranks themselves.  A class
        # whose top digit is pinned -- a counter with no leading zeros, which
        # is what a Zeckendorf-style representation is -- carries a constant
        # offset per width, and fitting the rank absolutely would have to
        # solve it away by setting the top weight to zero.  The difference
        # form is offset-free and asks only what one increment costs.
        for a, b in zip(ss, ss[1:]):
            eqs.append(([(b[i] if i < n else 0) - (a[i] if i < n else 0)
                         for i in range(maxW)], 1))
    if len(eqs) < 8 or not W:
        return None
    sol, bad = _solve([(c[:W], r) for c, r in eqs], W)
    if sol is None:
        return None
    # Keep the longest DETERMINED prefix.  A position that only ever appears
    # in the widest, half-observed class is not pinned by the equations, and
    # dropping the whole fit for it would throw away a numeration the machine
    # states perfectly at every width below.  Strings wider than the prefix
    # are then simply not read.
    w = []
    for x in sol:
        if x is None or x.denominator != 1 or x <= 0:
            break
        if w and int(x) < w[-1]:
            break                         # weights must not decrease
        w.append(int(x))
    if len(w) < 3:
        return None
    return {'weights': w, 'violated': round(bad / len(eqs), 4),
            'equations': len(eqs)}


def name_weights(w, b):
    if not w:
        return 'empty'
    if all(x == b ** i for i, x in enumerate(w)):
        return 'base-%d' % b
    if all(x == FIB[i] for i, x in enumerate(w)):
        return 'fibonacci'
    if all(x == FIB[i + 1] for i, x in enumerate(w)):
        return 'fibonacci(shifted)'
    return 'mixed'


def lag_stats(vals, steps=(1, 2, 3)):
    """Cheapest possible evidence for `+step`, for every step at once: the
    fraction of same-width pairs at lag 1, 2 or 3 that differ by exactly that
    step.  A row whose family members are every OTHER anchor visit shows
    nothing at lag 1 and everything at lag 2, so the lag is a maximum, not a
    fixed choice.  One pass per lag rather than one per (lag, step): this is
    the inner loop of the whole file."""
    out = {s: 0.0 for s in steps}
    for lag in (1, 2, 3):
        d = collections.Counter()
        tot = 0
        for a, b in zip(vals, vals[lag:]):
            if a is None or b is None or a[1] != b[1]:
                continue
            tot += 1
            d[b[0] - a[0]] += 1
        if tot >= 8:
            for s in steps:
                out[s] = max(out[s], d.get(s, 0) / tot)
    return out


def order_fit(vals, step):
    """Does the machine's OWN enumeration order agree with this numeration?

    Greedy chain-walking can always stitch some increasing subsequence out of
    a long enough walk, so it is not by itself evidence.  This is: inside a
    width class, take the distinct values in order of FIRST APPEARANCE and ask
    whether they are 0, step, 2*step, ...  Nothing is stitched, nothing is
    skipped, the interleaving of mid-flight visits is irrelevant because a
    repeat is not a new value, and a class that agrees is a class the counter
    walked in this numeration's order.

    Returns (classes read exactly, largest such class, classes monotone,
    classes seen).  `exact` is the strong claim; `monotone` is the weak one --
    the value never goes backwards inside a width, which is all that
    LADDER_PLAN sec.4g's question `is there a monotone quantity` asks for."""
    by = collections.OrderedDict()
    for v in vals:
        if v is None:
            continue
        by.setdefault(v[1], [])
        if v[0] not in by[v[1]]:
            by[v[1]].append(v[0])
    exact = mono = seen = 0
    big = 0
    for n, vs in by.items():
        if len(vs) < 4:
            continue
        seen += 1
        if all(b > a for a, b in zip(vs, vs[1:])):
            mono += 1
        # An arithmetic progression of difference `step` from wherever the
        # class starts.  Where it starts is the FILL law's business, not the
        # numeration's -- `Fill` in valfam.py already infers it -- so pinning
        # the first value to 0 here would reject a correct reading for a
        # reason that belongs to another constructor.
        if vs == [vs[0] + step * i for i in range(len(vs))]:
            exact += 1
            big = max(big, len(vs))
    return exact, big, mono, seen


def chain_skip(vals, step, window=8):
    """The longest chain of family MEMBERS, allowing NON-members between them.

    A member is a subsequence of the anchor visits -- the head crosses the
    anchor cell several times per increment, and on an interleaved row the
    crossings in between are perfectly decodable strings that are simply not
    the next member (LADDER_PLAN sec.4e, `observe_fill`).  So the chain is
    walked greedily with a window: from a member at (v, n) the next member is
    the first later visit at (v+step, n), or -- at a width change, which is
    the fill -- the first visit of a different width with a small value.

    Returns members on the chain, the longest run inside ONE width, the
    largest gap in visits between members, and the number of width changes
    crossed.  `run` is what `valfam._try_parse`'s `min_chain` counts, except
    that it counts CONSECUTIVE visits and this does not: the difference
    between the two numbers is the size of the engine gap."""
    n = len(vals)
    firsts = [i for i, v in enumerate(vals) if v is not None][:3]
    best = (0, 0, 0, 0, {})
    for s in firsts:
        cur = vals[s]
        members = run = longest = 1
        maxgap = widths = 0
        segs, lo, hi = {}, {}, {}
        j = s + 1
        while j < n:
            hi_k = min(n, j + window)
            # Same width FIRST, across the whole window.  A width change is
            # the fill, and the fill only fires at the top of a width; taking
            # the first visit that merely LOOKS like a reset -- a mid-flight
            # tape of the previous width, say -- derails the chain onto a
            # width it never left, which is how a real +1 reading reports a
            # run of three.
            found = next((k for k in range(j, hi_k)
                          if vals[k] is not None and vals[k][1] == cur[1]
                          and vals[k][0] == cur[0] + step), -1)
            if found >= 0:
                run += 1
            else:
                found = next((k for k in range(j, hi_k)
                              if vals[k] is not None and vals[k][1] > cur[1]
                              and vals[k][0] < 2 * step), -1)
                if found >= 0:
                    run, widths = 1, widths + 1
            if found < 0:
                break
            maxgap = max(maxgap, found - j)
            longest = max(longest, run)
            segs.setdefault(cur[1], [0])
            segs[cur[1]][0] = max(segs[cur[1]][0], run)
            lo[cur[1]] = min(lo.get(cur[1], cur[0]), cur[0])
            hi[cur[1]] = max(hi.get(cur[1], cur[0]), cur[0])
            cur, members, j = vals[found], members + 1, found + 1
        if members > best[0]:
            best = (members, longest, maxgap, widths,
                    {n: (v[0], lo[n], hi[n]) for n, v in segs.items()})
    return best


def readings(ctr, max_perm=6, maxl=2, keep=25):
    """Every (terminator, prefix, digit width, digit ordering, code, step,
    weight sequence) this file knows how to try, scored.

    The four things `find_families` fixes are varied INDEPENDENTLY of each
    other rather than in its nested order: the terminator comes off the whole
    walk rather than off one constant-far-side group and may be a SET, the
    base off the alphabet actually present, the code from {positional, gray},
    the step from {1, 2, 3} -- and the weight sequence, which the search does
    not have at all, is fitted."""
    import itertools
    sufs = suffixes(ctr)
    cands = []
    for tail in sufs + ['*']:
        for l in range(1, maxl + 1):
            # The near-head PREFIX runs past the digit width on purpose.
            # `valfam._try_parse` takes `p in range(l)`, so a one-cell digit
            # never gets a prefix at all -- and a machine whose lowest cell is
            # a phase bit rather than a digit (LADDER_PLAN sec.4g) is exactly
            # a one-cell-digit family with p = 1.
            for p in range(0, min(l + 2, 4)):
                if tail == '*':
                    if len(sufs) < 2:
                        continue
                    gp = grams_multi(ctr, l, p, sufs)
                else:
                    gp = [None if g is None else (g, 0)
                          for g in grams(ctr, l, p, tail)]
                if sum(1 for g in gp if g and g[0]) < 20:
                    continue
                alpha = sorted({x for g in gp if g for x in g[0]})
                if not (2 <= len(alpha) <= 3):
                    continue
                b = len(alpha)
                for perm in list(itertools.permutations(alpha))[:max_perm]:
                    idx = {a: i for i, a in enumerate(perm)}
                    ds = [None if g is None
                          else (tuple(idx[x] for x in g[0]), g[1]) for g in gp]
                    codes = {}
                    for code in ('binary', 'gray'):
                        vs = []
                        for e in ds:
                            if e is None:
                                vs.append(None)
                                continue
                            d, ph = e
                            dd = V.gray_decode(list(d), b) if code == 'gray' \
                                else list(d)
                            v = 0
                            for x in reversed(dd):
                                v = v * b + x
                            vs.append((v, len(d) * 10 + ph))
                        codes[code] = (vs, 'base-%d' % b,
                                       [b ** i for i in range(6)], 0.0)
                    fw = fit_weights([None if e is None else e[0]
                                      for e in ds])
                    if fw and fw['violated'] <= 0.05:
                        w = fw['weights']
                        vs = []
                        for e in ds:
                            if e is None or len(e[0]) > len(w):
                                vs.append(None)
                                continue
                            vs.append((sum(x * w[i] for i, x in
                                           enumerate(e[0])),
                                       len(e[0]) * 10 + e[1]))
                        codes['weights'] = (vs, name_weights(w, b), w,
                                            fw['violated'])
                    for code, (vs, nm, w, viol) in codes.items():
                        qs = lag_stats(vs)
                        for step in (1, 2, 3):
                            q = qs[step]
                            if q < 0.15:
                                continue
                            cands.append((q, {
                                'tail': (tail if tail == '*'
                                         else list(tail)),
                                'prefix': p, 'digit_len': l, 'base': b,
                                'code': code, 'step': step, 'numeration': nm,
                                'weights': w, 'lag_stat': round(q, 3),
                                'violated': viol, 'vals': vs}))
    cands.sort(key=lambda c: -c[0])
    out = []
    for _, r in cands[:keep]:
        vs = r.pop('vals')
        mem, run, gap, wid, segs = chain_skip(vs, r['step'])
        ex, big, mono, seen = order_fit(vs, r['step'])
        dec = sum(1 for v in vs if v is not None)
        # A width class is COMPLETE when the chain walked it from the bottom
        # to the top string the weights allow.  Completeness is what
        # distinguishes a reading from a lucky stitch: a greedy walk with a
        # window can always find SOME increasing subsequence, but it cannot
        # make an incomplete class enumerate every one of its strings in
        # order.  `numsys.py` measures the same thing without a reader.
        w, b = r['weights'], r['base']
        comp = 0
        for n10, (rn, vlo, vhi) in segs.items():
            if rn >= 4 and vhi - vlo == r['step'] * (rn - 1):
                comp += 1
        r.update({'members': mem, 'run': run, 'max_gap': gap,
                  'widths_crossed': wid, 'decodable': dec,
                  'visits': len(vs), 'complete_widths': comp,
                  'exact_classes': ex, 'largest_class': big,
                  'mono_classes': mono, 'classes_seen': seen,
                  'density': round(mem / max(1, len(vs)), 3)})
        # What the CURRENT search could see: members must be CONSECUTIVE
        # anchor visits inside one constant-far-side group, the code one of
        # its two, the step 1 or 2, and the terminator single.
        r['in_search'] = bool(r['numeration'].startswith('base-')
                              and r['code'] in ('binary', 'gray')
                              and r['step'] in (1, 2) and gap == 0
                              and r['tail'] != '*' and run >= 8)
        out.append(r)
    out.sort(key=lambda r: (-r['exact_classes'], -r['largest_class'],
                            -r['complete_widths'], -r['members']))
    return out


def binomial_probe(ctr):
    """A numeration a WEIGHT SEQUENCE still cannot express.

    One row of the fifteen enumerates, for each width, every string of each
    POPCOUNT -- C(n-1, k-1) of them -- and walks each popcount class in colex
    order.  That is the binomial (combinadic) number system: the value of a
    string is `sum_j C(p_j, j+1)` over the positions `p_j` of its set cells,
    and the weight of a set cell depends on its RANK among the set cells, not
    on its position alone.  No `w_i` can say that, so it is measured
    separately rather than folded into `fit_weights`.

    The class key is `(width, popcount)`: the popcount is carried on the FAR
    side, which is why the row also reads as `far side is a second counter`."""
    from math import comb
    vals = []
    for c in ctr:
        if not c or c[-1] != 1:
            vals.append(None)
            continue
        ones = [i for i, x in enumerate(c[:-1]) if x == 1]
        r = sum(comb(p, j + 1) for j, p in enumerate(ones))
        vals.append((-r, (len(c), sum(c))))
    ex, big, mono, seen = order_fit(vals, 1)
    return {'exact_classes': ex, 'largest_class': big,
            'mono_classes': mono, 'classes_seen': seen}


def unary_probe(ctr, far, maxL=4, maxT=12):
    """The counter side as a RUN TEMPLATE: `prefix . word^p . tail`.

    Read off John's tape of `1RB0RB_1LC0RC_1RA0LD_0LB0LC`: *"once you get past
    a certain point the count seems to be the number of 011 stripes"*, and
    that is a counter whose value is `p` and whose alphabet has ONE digit.

    `Fam` cannot hold it.  `_try_parse` requires `2 <= len(alpha) <= 3`,
    because `Fam.b = len(digs)` is a radix and a base-1 positional numeration
    is degenerate -- so a unary counter is rejected before any base, code,
    step or terminator is tried.  But `word^(a*p + b)` is exactly the shape
    §4e already fits on the FAR side (`fit_far`); the gap is that it is
    available there and not on the counter side.

    Reports, for the best (word, tail): how many visits parse, the range of
    `p`, whether `p` is monotone over the walk, how many distinct prefixes
    occur -- and, the finite-phase test, whether the prefix set at LARGE `p`
    is the same set as at small `p`.  A bounded prefix set means the row is a
    one-parameter family with a finite control state, not a value counter."""
    if not ctr:
        return None
    S = max(ctr, key=len)
    best = None
    for T in range(0, min(maxT, len(S) - 1) + 1):
        t = S[len(S) - T:] if T else ()
        for L in range(1, maxL + 1):
            if len(S) < T + L:
                continue
            w = S[len(S) - T - L:len(S) - T]
            if not any(w):
                continue
            rec = []
            for i, s in enumerate(ctr):
                if T and s[len(s) - T:] != t:
                    continue
                e = len(s) - T
                p = 0
                while e >= L and s[e - L:e] == w:
                    p += 1
                    e -= L
                if p:
                    rec.append((p, s[:e], len(far[i])))
            if len(rec) < 20:
                continue
            ps = [r[0] for r in rec]
            pre = {r[1] for r in rec}
            hi_p = max(ps)
            lo_set = {r[1] for r in rec if r[0] <= hi_p // 3}
            hi_set = {r[1] for r in rec if r[0] >= 2 * hi_p // 3}
            got = {'word': ''.join(map(str, w)),
                   'tail': ''.join(map(str, t)),
                   'parsed': len(rec), 'visits': len(ctr),
                   'p_min': min(ps), 'p_max': hi_p,
                   'monotone': all(b >= a for a, b in zip(ps, ps[1:])),
                   'increments': sorted(set(b - a for a, b in zip(ps, ps[1:]))
                                        )[:4],
                   'prefixes': len(pre),
                   'phases_shared': len(lo_set & hi_set),
                   'phases_low': len(lo_set), 'phases_high': len(hi_set),
                   'far_affine': _far_affine(rec)}
            # Ranked by what makes it a FAMILY, not by how big p gets: a
            # bare run of 1s inside a bouncer also gives a monotone p, and
            # what separates the real reading from it is that the far side is
            # affine in p and that the prefix set at large p is the SAME
            # finite set as at small p -- a control state, not a growing one.
            key = (got['monotone'], got['far_affine'] is not None,
                   got['phases_shared'] == got['prefixes'],
                   set(got['increments']) <= {0, 1},
                   -len(pre), hi_p)
            if best is None or key > best[0]:
                best = (key, got)
    return best[1] if best else None


def _far_affine(rec):
    """Is the far side's LENGTH affine in p?  That is §4e's `a*p + b` measured
    without a template: if it holds, the row is one-parameter on both sides."""
    by = {}
    for p, _, fl in rec:
        by.setdefault(p, []).append(fl)
    ks = sorted(by)
    if len(ks) < 4:
        return None
    mins = [(k, min(by[k])) for k in ks]
    d = {b - a for (_, a), (_, b) in zip(mins, mins[1:])}
    if len(d) == 1:
        a = d.pop()
        return {'a': a, 'b': mins[0][1] - a * mins[0][0]}
    return None


# ------------------------------------------------- pass 3: the other side

def far_class(far, ctr):
    """Taxonomy of the far side at this anchor.

    `constant`            -- one cell string; the one-parameter family.
    `template`            -- the run WORDS are constant and one count moves;
                             §4e's word^(a p + b), which `fit_far` fits.
    `second counter`      -- the far side's own successor is a function of it,
                             so it is a counter in its own right and the row
                             needs a genuinely two-sided model.
    `bounded oscillation` -- finitely many far sides, revisited, but no
                             functional successor.
    `unbounded`           -- distinct far sides keep appearing.
    """
    pop = collections.Counter(far)
    mx = pop.most_common(1)[0][1] if pop else 0
    if len(pop) == 1:
        kind = 'constant'
    else:
        wt = [tuple(w for w, _ in V.block_rle(list(f))) for f in far]
        wpop = collections.Counter(wt)
        wmax = wpop.most_common(1)[0][1]
        st = successor_test(far)
        grow = len(pop) / max(1, len(far))
        if wmax >= 0.9 * len(far) and len(pop) <= 0.5 * len(far):
            kind = 'template'
        elif st and st['states_with_unique_successor'] >= 0.9:
            kind = 'second counter'
        elif grow < 0.25:
            kind = 'bounded oscillation'
        else:
            kind = 'unbounded'
    lens = [len(f) for f in far]
    mono = all(a <= b for a, b in zip(lens, lens[1:]))
    return {'kind': kind, 'distinct': len(pop), 'max_group': mx,
            'len_monotone': mono, 'visits': len(far),
            'both_sides_grow': (len(set(len(c) for c in ctr)) > 3
                                and len(set(lens)) > 3)}


def anchor_probe(tm, steps=60000, cap=4000):
    """Is the ANCHOR the wrong idea for this row?

    A `(state, head)` visit is one choice of recurring configuration.  Two
    cheaper-to-check alternatives are measured here, both strictly finer:

      `(state, head, k cells of context)` -- the head passes the same cell in
      several distinct local situations, and a counter step is only one of
      them; refining the anchor by context separates them.

      `record` -- the visit at which the head reaches a cell it has never
      reached before.  A machine whose repeating unit is a SWEEP, not a cell
      visit, has a clean successor here and none at any (state, head).

    Reports the best `states_with_unique_successor` each definition gets on
    the counter side, so `the anchor is wrong` becomes a number."""
    tape, pos, cq, lo, hi = {}, 0, 0, 0, 0
    ctxs = collections.defaultdict(list)
    rec = []
    for _ in range(steps):
        cell = tape.get(pos, 0)
        c1 = (tape.get(pos - 1, 0), tape.get(pos + 1, 0))
        key = (cq, cell, c1)
        if len(ctxs[key]) < cap:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            ctxs[key].append((tuple(gl), tuple(gr)))
        tr = tm.get((cq, cell))
        if tr is None:
            break
        w, d, cq = tr
        tape[pos] = w
        pos += d
        if pos < lo or pos > hi:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - min(lo, pos))]
            gr = [tape.get(pos + 1 + i, 0) for i in range(max(hi, pos) - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            if len(rec) < cap:
                rec.append((tuple(gl), tuple(gr)))
        lo, hi = min(lo, pos), max(hi, pos)
    best = {'context_anchor': 0.0, 'record_anchor': 0.0}
    for key, vs in ctxs.items():
        if len(vs) < 40:
            continue
        for i in (0, 1):
            st = successor_test([v[i] for v in vs])
            if st:
                best['context_anchor'] = max(
                    best['context_anchor'], st['states_with_unique_successor'])
    for i in (0, 1):
        if len(rec) >= 40:
            st = successor_test([v[i] for v in rec])
            if st:
                best['record_anchor'] = max(
                    best['record_anchor'], st['states_with_unique_successor'])
    best['record_visits'] = len(rec)
    return best


# ------------------------------------------------------------------ driver

def analyze(spec, visits=1500, steps=200000, top=8):
    t0 = time.time()
    tm = parse_tm(spec)
    V._WALKS.clear()
    out = {'spec': spec, 'anchors': []}
    named = {}
    try:
        snaps = simulate(tm, 20000)
        from discover import mine_shapes, build_ladder
        rules = build_ladder(tm, mine_shapes(snaps), time_cap=25.0)
        named = V.digit_words(rules)
    except Exception as e:                                  # noqa: BLE001
        out['ladder_error'] = str(e)
    out['ladder_digits'] = [''.join(map(str, w)) for w in named]
    for q, h in anchors(tm, steps, top=top):
        for side, (ctr, far) in sides(tm, q, h, steps).items():
            ctr, far = ctr[:visits], far[:visits]
            if len(ctr) < 40 or len(set(ctr)) < 4:
                continue
            st = successor_test(ctr)
            rec = {'anchor': '%s%d' % (chr(65 + q), h), 'side': side,
                   'visits': len(ctr), 'successor': st,
                   'far': far_class(far, ctr),
                   'classes': width_classes(ctr),
                   'growth': growth_ratio(width_classes(ctr))}
            rec['readings'] = readings(ctr)[:4]
            rec['binomial'] = binomial_probe(ctr)
            rec['unary'] = unary_probe(ctr, far)
            out['anchors'].append(rec)
    out['anchor_probe'] = anchor_probe(tm)
    best = None
    for a in out['anchors']:
        for r in a['readings']:
            k = (r['exact_classes'], r['largest_class'], r['members'])
            if best is None or k > (best[1]['exact_classes'],
                                    best[1]['largest_class'],
                                    best[1]['members']):
                best = (a, r)
    if best:
        out['best'] = dict(best[1], anchor=best[0]['anchor'],
                           side=best[0]['side'],
                           far=best[0]['far']['kind'])
    up = [a['unary'] for a in out['anchors'] if a['unary']]
    up = [u for u in up if u['monotone'] and u['p_max'] >= 8
          and u['far_affine'] is not None
          and u['phases_shared'] == u['prefixes']
          and set(u['increments']) <= {0, 1}]
    out['unary_best'] = max(up, key=lambda u: (-u['prefixes'], u['p_max']),
                            default=None)
    bp = max((a['binomial'] for a in out['anchors']),
             key=lambda d: (d['exact_classes'], d['largest_class']),
             default=None)
    out['binomial_best'] = bp
    out['seconds'] = round(time.time() - t0, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('list')
    ap.add_argument('--json')
    ap.add_argument('--visits', type=int, default=1500)
    ap.add_argument('--top', type=int, default=8)
    a = ap.parse_args()
    specs = [l.split()[0] for l in open(a.list) if l.strip()]
    res = []
    for s in specs:
        r = analyze(s, visits=a.visits, top=a.top)
        res.append(r)
        b = r.get('best')
        sm = ('%-20s %s%s stp=%d tl=%-3s ex=%-2d big=%-4d mem=%-4d gap=%d %s'
              % (b['numeration'] + '/' + b['code'], b['anchor'], b['side'],
                 b['step'], ''.join(map(str, b['tail'])) or '-',
                 b['exact_classes'], b['largest_class'],
                 b['members'], b['max_gap'], b['far'])
              ) if b else 'NO MONOTONE READING'
        bf = max((x['successor']['states_with_unique_successor']
                  for x in r['anchors'] if x['successor']), default=0.0)
        bp = r.get('binomial_best') or {}
        if (bp.get('exact_classes', 0) >= 5
                and (not b or bp['largest_class'] > b['largest_class'])):
            sm = ('%-20s        stp=1 tl=-   ex=%-2d big=%-4d binomial'
                  % ('binomial/combinadic', bp['exact_classes'],
                     bp['largest_class']))
        up = r.get('unary_best')
        if up and (not b or up['p_max'] > b['largest_class']):
            sm = ('%-20s        stp=1 tl=%-7s p=1..%-3d phases=%-3d unary'
                  % ('unary/' + up['word'], up['tail'][:7], up['p_max'],
                     up['prefixes']))
        print('%-30s %-78s succ=%.2f ctx=%.2f rec=%.2f %ss'
              % (s, sm, bf, r['anchor_probe']['context_anchor'],
                 r['anchor_probe']['record_anchor'], r['seconds']))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            for r in res:
                f.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    main()
