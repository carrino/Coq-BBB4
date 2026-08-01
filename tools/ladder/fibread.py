#!/usr/bin/env python3
"""UNTRUSTED.  ROUTE A of LADDER_PLAN 4s: is the F(1,1) reading available?

Wave 4s read the six surviving fibonacci rows for the first time (`valfam.py
--numeration`) and every one of them came back at weights `1, 2, 3, 5, 8, 13`
-- Zeckendorf -- while `LadderCheck` 11 states the numeration at
`1, 1, 2, 3, 5, 8`.  Its closing advice was: before building a fourth
`(code, step)` pair, check whether these anchors ALSO admit the reading the
kernel already speaks, because twice now (the gray rows, 4p's `HIGHER` label)
a gate read as a statement about the machine turned out to be a statement
about which of several equally-good readings the tooling handed the emitter.

This is that check, and it is a MEASUREMENT and not a search: it re-runs
`find_families` with the numeration pass forced on, and prints EVERY family
that came back weighted, with the weights `fit_weights` fitted, the anchor it
was read at, and the chain.  If a `1, 1, 2, 3, 5` family is in the list, the
kernel can already state the row and there is nothing to build; if every
weighted family at every anchor is Zeckendorf, the shifted numeration is a
property of the machines and Route B is the only way in.

`--all-perms` additionally reports, per anchor, the raw weight tuple of every
digit-permutation that fits at all -- not only the ones that survive
`_try_parse`'s +1-per-visit chain test -- so a reading that the chain test
rejects still shows up as evidence about the numeration itself.

Nothing here carries proof weight.
"""

import argparse
import itertools
import json
import sys
import time
from collections import Counter, defaultdict

import valfam
from valfam import (fit_classes, fit_weights, name_weights, runs_cells,
                    _grams, _tail_cands, _widths, digit_words, rots)
from engine import parse_tm
from trace import simulate

ROWS = [
    '1RB---_0LC1RD_1LB1RC_1LB0RD',
    '1RB---_0LC1RD_1LB1RD_1LB0RD',
    '1RB---_1LC0RB_0LD1RB_1LC1RB',
    '1RB---_1LC0RB_0LD1RB_1LC1RD',
    '1RB---_1LC1RB_0LB1RD_1LC0RD',
    '1RB---_1LC1RD_0LB1RD_1LC0RD',
]

def _fib(a, b, n=24):
    out = []
    for _ in range(n):
        out.append(a)
        a, b = b, a + b
    return tuple(out)


FIB11 = _fib(1, 1)          # what LadderCheck 11 states
FIB12 = _fib(1, 2)          # what wave 4s measured: Zeckendorf


def shape(w):
    """Name the weight tuple against the two fibonacci ladders."""
    if w is None:
        return 'none'
    if tuple(w) == FIB11[:len(w)]:
        return 'F(1,1)'
    if tuple(w) == FIB12[:len(w)]:
        return 'F(1,2)/Zeckendorf'
    return 'other'


def build(spec, steps):
    tm = parse_tm(spec)
    snaps = simulate(tm, steps)
    from discover import mine_shapes, build_ladder
    rules = build_ladder(tm, mine_shapes(snaps), time_cap=60.0)
    return tm, snaps, rules


def families(spec, steps):
    """Every family `find_families` returns with the numeration forced."""
    tm, snaps, rules = build(spec, steps)
    fams = valfam.find_families(tm, snaps, rules, numeration=True)
    out = []
    for fam, ft, chain in fams:
        w = None if fam.weights is None else tuple(fam.weights)
        out.append({'q': 'ABCD'[fam.q], 'h': fam.h, 'side': fam.side,
                    'chain': chain, 'first_t': ft, 'l': fam.l, 'p': len(fam.pre),
                    'tail': list(fam.tail), 'code': fam.code, 'step': fam.step,
                    'weights': None if w is None else list(w),
                    'numeration': name_weights(fam.weights, fam.b),
                    'shape': shape(w)})
    return out


def raw_perms(spec, steps, max_anchor=6, min_chain=8, max_occ=900):
    """Every (anchor, digit width, prefix, terminator, permutation) whose digit
    strings admit a weight fit at all -- `_weights_pass`'s inner loop, with the
    chain test and the class fit taken OFF, so a reading the family builder
    rejects is still reported.  The question Route A asks is about the
    NUMERATION, and the numeration is decided before either of those."""
    tm, snaps, rules = build(spec, steps)
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
    order = sorted(byqh.items(), key=lambda kv: -len(kv[1]))[:max_anchor]
    hits, seen = [], set()
    for (q, h), full in order:
        if len(full) < min_chain:
            continue
        for side in ('L', 'R'):
            occ = full[:max_occ]
            cs, os = [], []
            for _, s in occ:
                c = runs_cells(s[2] if side == 'L' else s[3])
                o = runs_cells(s[3] if side == 'L' else s[2])
                cs.append(c)
                os.append(tuple(o) if o is not None else None)
            pop = Counter(o for o in os if o is not None)
            for other, n in pop.most_common(2):
                if n < min_chain:
                    break
                sel = [i for i in range(len(occ)) if os[i] == other]
                strs = [cs[i] for i in sel if cs[i]]
                for l in lens[:2]:
                    for tail in _tail_cands(strs, l):
                        for p in range(l + 2):
                            grams, _ = _grams(cs, sel, l, p, tail)
                            alpha = sorted({x for g in grams if g for x in g})
                            if not (2 <= len(alpha) <= 3):
                                continue
                            for perm in itertools.permutations(alpha):
                                idx = {a: i for i, a in enumerate(perm)}
                                ds = [None if g is None
                                      or any(x not in idx for x in g)
                                      else tuple(idx[x] for x in g)
                                      for g in grams]
                                obs, sn = {}, set()
                                for d in ds:
                                    if not d or d in sn:
                                        continue
                                    sn.add(d)
                                    obs.setdefault(len(d), []).append(d)
                                ks = sorted(obs)
                                if len(ks) < 4 or ks != list(range(1, ks[-1] + 1)):
                                    continue
                                w = fit_weights([d for d in ds if d])
                                if w is None:
                                    continue
                                key = (q, h, side, l, p, tail, tuple(w))
                                if key in seen:
                                    continue
                                seen.add(key)
                                hits.append(
                                    {'q': 'ABCD'[q], 'h': h, 'side': side,
                                     'l': l, 'p': p, 'tail': list(tail),
                                     'perm': [list(x) for x in perm],
                                     'weights': list(w),
                                     'classes_fit': fit_classes(obs) is not None,
                                     'shape': shape(w)})
    return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--steps', type=int, default=20000)
    ap.add_argument('--all-perms', action='store_true')
    ap.add_argument('--json')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else ROWS
    out = []
    for spec in specs:
        t0 = time.time()
        rec = {'spec': spec}
        rec['families'] = families(spec, a.steps)
        if a.all_perms:
            rec['perms'] = raw_perms(spec, a.steps)
        rec['seconds'] = round(time.time() - t0, 1)
        out.append(rec)
        wf = [f for f in rec['families'] if f['weights']]
        print('%-30s %d families, %d weighted, shapes %s  (%.0fs)' % (
            spec, len(rec['families']), len(wf),
            dict(Counter(f['shape'] for f in wf)) or '-', rec['seconds']))
        for f in wf:
            print('    q=%s h=%d %s chain=%-4d l=%d p=%d tail=%s  %s  %s'
                  % (f['q'], f['h'], f['side'], f['chain'], f['l'], f['p'],
                     f['tail'], f['weights'][:6], f['shape']))
        if a.all_perms:
            sh = Counter(x['shape'] for x in rec['perms'])
            print('    raw weight fits: %s' % dict(sh))
            for x in rec['perms']:
                if x['shape'] != 'F(1,2)/Zeckendorf':
                    print('      q=%s h=%d %s l=%d p=%d tail=%s cls=%s %s %s'
                          % (x['q'], x['h'], x['side'], x['l'], x['p'],
                             x['tail'], x['classes_fit'], x['weights'][:6],
                             x['shape']))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            for r in out:
                f.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    main()
