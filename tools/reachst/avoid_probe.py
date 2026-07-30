#!/usr/bin/env python3
"""UNTRUSTED probe behind docs/REACHST_TIER.md.

Three measurements, one command each:

  --sparse       state-usage counts over T steps: which state is the liveness
                 question (the one that fires logarithmically often).
  --tables       enumerate the DISTINCT q-avoiding sub-machines over a row
                 list x 4 states, and test each EXHAUSTIVELY for termination
                 over every tape of width <= W with blanks outside, every head
                 position, every start state.
  --bounded      is there a uniform STEP BOUND for each avoid sub-machine?
                 (symbolic search branching on every freshly-read cell).

Nothing here carries proof weight; the Coq kernel re-checks every board.
"""
import argparse
import itertools
from collections import defaultdict

LAB = 'ABCD'


def parse(spec):
    tab = {}
    for qi, part in enumerate(spec.split('_')):
        for s in (0, 1):
            f = part[3 * s:3 * s + 3]
            tab[(qi, s)] = (None if f in ('---', '1RZ')
                            else (int(f[0]), 1 if f[1] == 'R' else -1, LAB.index(f[2])))
    return tab


def usage(spec, T):
    tab = parse(spec)
    tape = defaultdict(int)
    p, q = 0, 0
    cnt = defaultdict(int)
    for _ in range(T):
        cnt[q] += 1
        tr = tab[(q, tape[p])]
        if tr is None:
            break
        tape[p] = tr[0]
        p += tr[1]
        q = tr[2]
    return cnt


def avoid_table(tab, qa):
    return {(q, s): (None if (tr is None or tr[2] == qa) else tr)
            for (q, s), tr in sorted(tab.items()) if q != qa}


def show(t):
    return ' '.join(
        '%s%d->%s' % (LAB[q], s, 'HALT' if t[(q, s)] is None else
                      '%d%s%s' % (t[(q, s)][0], 'R' if t[(q, s)][1] > 0 else 'L',
                                  LAB[t[(q, s)][2]]))
        for (q, s) in sorted(t))


def terminates(t, W, T=4 * 10 ** 6):
    """exhaustive over tapes of width <= W (blank outside)."""
    states = sorted(set(q for (q, s) in t))
    for w in range(W + 1):
        for bits in (range(1 << w) if w else [0]):
            base = {i: (bits >> i) & 1 for i in range(w)}
            for p0 in range(-1, w + 1):
                for s0 in states:
                    tape = defaultdict(int, base)
                    p, q = p0, s0
                    for _ in range(T):
                        tr = t[(q, tape[p])]
                        if tr is None:
                            break
                        tape[p] = tr[0]
                        p += tr[1]
                        q = tr[2]
                    else:
                        return False, (w, bits, p0, LAB[s0])
    return True, None


def bounded(t, depth):
    """uniform step bound: branch on every freshly-read (unknown) cell."""
    stack = [(q, 0, {}, 0) for q in sorted(set(q for (q, s) in t))]
    worst = 0
    while stack:
        q, p, known, n = stack.pop()
        if n > depth:
            return False, None
        v = known.get(p)
        for b in ([0, 1] if v is None else [v]):
            tr = t[(q, b)]
            if tr is None:
                worst = max(worst, n + 1)
                continue
            k2 = dict(known)
            k2[p] = tr[0]
            stack.append((tr[2], p + tr[1], k2, n + 1))
    return True, worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('--sparse', action='store_true')
    ap.add_argument('--tables', action='store_true')
    ap.add_argument('--bounded', action='store_true')
    ap.add_argument('-T', type=int, default=200000)
    ap.add_argument('-W', type=int, default=10)
    ap.add_argument('--depth', type=int, default=40)
    a = ap.parse_args()
    specs = open(a.list).read().split()

    if a.sparse:
        for m in specs:
            c = usage(m, a.T)
            sp = min(range(4), key=lambda i: c[i])
            print('%s sparse=%s %s' % (
                m, LAB[sp], ' '.join('%s=%d' % (LAB[i], c[i]) for i in range(4))))

    if a.tables or a.bounded:
        cache = {}
        rows = []
        for m in specs:
            tab = parse(m)
            cells = []
            for qa in range(4):
                key = show(avoid_table(tab, qa))
                if key not in cache:
                    at = avoid_table(tab, qa)
                    cache[key] = (terminates(at, a.W) if a.tables else (None, None),
                                  bounded(at, a.depth) if a.bounded else (None, None))
                (ok, cex), (bd, worst) = cache[key]
                cells.append('%s:%s%s' % (LAB[qa],
                                          {True: 'T', False: 'F', None: '-'}[ok],
                                          '' if bd is None else
                                          ('/b%d' % worst if bd else '/-')))
            rows.append((m, cells))
            print('%s  %s' % (m, ' '.join(cells)))
        print('\n%d distinct avoid tables' % len(cache))
        if a.tables:
            print('%d terminate exhaustively (W<=%d)'
                  % (sum(1 for v in cache.values() if v[0][0]), a.W))
            for k, v in sorted(cache.items()):
                if v[0][0] is False:
                    print('  NONTERM %s  cex(w,bits,pos,state)=%s' % (k, v[0][1]))
        if a.bounded:
            print('%d have a uniform step bound at depth %d'
                  % (sum(1 for v in cache.values() if v[1][0]), a.depth))


if __name__ == '__main__':
    main()
