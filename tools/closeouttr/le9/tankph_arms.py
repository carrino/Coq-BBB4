#!/usr/bin/env python3
"""LE9 (UNTRUSTED, exploratory): derive every arm of a phased-tank model.

A model (JSON): spec, anchor [q, hs, side], pre, D (two digit words), T (tank
word), phases: [{suf, cz, z, cm, a, nxt}].  Prints, per arm class, the first
(threshold, stride) at which every arm derives.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import emit_step as S  # noqa: E402
from emit_step import NoClosure, blk, ARM_GRID, Arms  # noqa: E402


def cells(s):
    return tuple(int(ch) for ch in s)


def model_arms(m, tab, verbose=True):
    q, hs, side = m['anchor']
    left = side == 'L'
    OTHER = ((), (), 0, 0, ())
    pre = cells(m['pre'])
    D = [cells(w) for w in m['D']]
    T = cells(m['T'])
    derive = Arms(tab).derive
    el, er = (not left), left

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    def first(fn, grid, what):
        for n0, st in grid:
            g = fn(n0, st)
            if g is not None:
                return g, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % what)

    def inter_at(n0, st):
        got = []
        for r in range(n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[1] * r, D[1], s_, D[0]))
            c1 = conf(blk(pre + D[0] * r, D[0], s_, D[1]))
            try:
                got.append((r, c0, c1, derive(el, er, c0, c1, 'interior r=%d' % r)))
            except NoClosure:
                return None
        return got

    def wid_at(n0, st):
        got = []
        for r in range(n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[1] * r, D[1], s_, T))
            c1 = conf(blk(pre + D[0] * r, D[0], s_, D[1]))
            try:
                got.append((r, c0, c1, derive(el, er, c0, c1, 'widening r=%d' % r)))
            except NoClosure:
                return None
        return got

    out = {}
    out['inter'] = first(inter_at, ARM_GRID, 'interior')
    if any(p['tank'] for p in m['phases']):
        out['wid'] = first(wid_at, ARM_GRID, 'widening')
    fills = []
    for pi, ph in enumerate(m['phases']):
        suf = cells(ph['suf'])
        nx = m['phases'][ph['nxt']]
        suf2 = cells(nx['suf'])
        Z = tuple(c for dg in ph['z'] for c in D[dg])

        def fill_at(n0, st):
            got = []
            for r in range(1, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D[1] * r, D[1], s_, suf))
                hit = None
                if ph['cz']:
                    c1s = [(r, 0, conf(blk(pre + D[0] * r, D[0], s_, Z + T * ph['a'] + suf2)))]
                elif ph['cm']:
                    c1s = [(r, f1, conf(blk(pre + Z + T * f1, T, s_, T * (r + ph['a'] - f1) + suf2)))
                           for f1 in S._splits(r + ph['a'])]
                else:
                    c1s = [(r, 0, conf(blk(pre + Z + T * ph['a'], (), 0, suf2)))]
                for _r, f1, c1 in c1s:
                    try:
                        hit = (r, f1, c0, c1, derive(True, True, c0, c1, 'fill p%d r=%d' % (pi, r)))
                        break
                    except NoClosure:
                        continue
                if hit is None:
                    if verbose:
                        print('   phase %d r=%d st=%d: no program' % (pi, r, st), file=sys.stderr)
                    return None
                got.append(hit)
            return got
        grid1 = [(n0, st) for n0, st in ARM_GRID if n0 >= 1]
        fills.append(first(fill_at, grid1, 'fill phase %d' % pi))
    out['fills'] = fills
    return out


def main():
    m = json.loads(open(sys.argv[1]).read()) if sys.argv[1].endswith('.json') else json.loads(sys.argv[1])
    tab = S.E.parse_tm(m['spec'])
    S.E.TR_PINS = S.E.unfired(m['spec'], 10 ** 6)
    try:
        out = model_arms(m, tab)
    except NoClosure as e:
        print('FAIL', e)
        return 1
    print('inter n0=%d st=%d' % out['inter'][1:])
    if 'wid' in out:
        print('wid n0=%d st=%d' % out['wid'][1:])
    for i, f in enumerate(out['fills']):
        print('fill %d n0=%d st=%d' % ((i,) + f[1:]))
    return 0


if __name__ == '__main__':
    sys.exit(main())
