#!/usr/bin/env python3
"""TriGlueTr families on an exponent LATTICE (UNTRUSTED finder), for the BL
workstream (SCOPING_INSTR.md §7.4.BL).

    python3 tools/closeouttr/bl_ti.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 120]
        [--maxfam 120] [--maxleaf 600] [--maxsteps 4000] [--t0 3000] [--plist 1,2,3,4,6]
    python3 tools/closeouttr/bl_ti.py batch OUT.jsonl [...] --tag BL [--chunk 20]

`ti_batch.py` gives every family variable the domain [lb, oo): a block
[u^(lb + x)].  On the doubling bouncers that makes the exploration diverge:
a block that is always, say, 2 mod 4 long at a family's anchor is explored
at every length, and the lengths the machine never produces (the odd ones)
open new block shapes, which open more.  Here a family variable carries a
LATTICE [c + g*x] instead (TriGlueTr's exponents are affine, so the
checker takes it as is):

  * a family is created with [g = 0] for every variable (the one value
    seen);
  * a leaf whose end exponent is [e(z) = e0 + sum m_i z_i] widens the
    target's lattice to [c' = min(c, e0)], [g' = gcd(g, m_i, e0 - c)] (the
    family is re-explored, as ti_batch re-explores a lowered bound);
  * the leaf's target value is [(e(z) - c') / g'], affine in [z].

The lattices only coarsen, so the exploration terminates or hits the
family cap.  Everything else (leaf runs, the chain search, the rankings
and every replayed check) is ti_batch's, and the certificate is a plain
[tcert] for [tri_sound]: a wrong one fails to compile, it cannot mis-prove.
"""
import argparse
import json
import math
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ti_batch as T                            # noqa: E402

C = T.C


SEEDS = {}          # family key -> (c, g) from the concrete pass
ASTEPS = 3000       # leaf steps of the concrete pass
G0 = 1              # lattice step of a variable the concrete pass saw once (or not at all)


class LFam(T.Fam):
    """a family whose variable k stands for the exponent c[k] + g[k] * x_k"""

    def __init__(self, key, vals):
        super().__init__(key, vals)
        # G0 = 0: a variable seen once (or a family the concrete pass never
        # met) starts as the one value; G0 = 1: as [lb, oo); G0 = 2 (mixed):
        # the one value if the pass met the family, [lb, oo) if it did not
        self.c = list(vals)
        self.g = [0 if G0 == 0 else 1] * len(vals)
        if key in SEEDS and len(SEEDS[key][0]) == len(vals):
            self.c = list(SEEDS[key][0])
            self.g = [g or (1 if G0 == 1 else 0) for g in SEEDS[key][1]]
            self.lb = list(self.c)

    def pattern(self):
        k = 0
        out = []
        for sh in (self.sL, self.sR):
            side = []
            for s in sh:
                if s[0] == 'L':
                    side.append(s)
                else:
                    g = self.g[k]
                    side.append(('B', s[1], (self.c[k], ((k, g),) if g else ())))
                    k += 1
            out.append(side)
        return out

    def widen(self, e):
        """widen variable lattices to hold the exponents e (aexps); True if changed"""
        ch = False
        for k, (e0, lin) in enumerate(e):
            c, g = self.c[k], self.g[k]
            g2 = g
            for _, m in lin:
                g2 = math.gcd(g2, m)
            c2 = min(c, e0)
            g2 = math.gcd(g2, abs(e0 - c))
            if (c2, g2) != (c, g):
                self.c[k], self.g[k] = c2, g2
                ch = True
        self.lb = list(self.c)
        return ch

    def value(self, e):
        """the target values (e - c) / g as aexps"""
        out = []
        for k, (e0, lin) in enumerate(e):
            c, g = self.c[k], self.g[k]
            if g == 0:
                if lin or e0 != c:
                    raise T.Fail('lattice')
                out.append((0, ()))
                continue
            if (e0 - c) % g or any(m % g for _, m in lin):
                raise T.Fail('lattice')
            out.append(((e0 - c) // g, tuple((i, m // g) for i, m in lin)))
        return out


class LExplorer(T.Explorer):
    def fam_of(self, q, h, L, R):
        L = T.generalize(L)
        R = T.generalize(R)
        key = (q, h, T.shape(L), T.shape(R))
        ex = T.exps(L) + T.exps(R)
        if key not in self.fidx:
            if len(self.fams) >= T.MAXFAM:
                raise T.Fail('too many families')
            self.fidx[key] = len(self.fams)
            F = LFam(key, [e[0] for e in ex])
            F.widen(ex)
            self.fams.append(F)
            return self.fidx[key], ex, True
        fid = self.fidx[key]
        F = self.fams[fid]
        return fid, ex, F.widen(ex)

    def explore(self, boot):
        q, L, h, R = boot
        f0, ex0, _ = self.fam_of(q, h, L, R)
        self.boot = (f0, ex0)
        todo = [f0]
        while todo:
            fid = todo.pop(0)
            if fid in todo:
                continue
            self.explore_fam(fid, todo)

    def explore_fam(self, fid, todo):
        F = self.fams[fid]
        st0 = (list(F.c), list(F.g))
        super().explore_fam(fid, todo)
        if (F.c, F.g) != st0 and fid in self.trees:
            # widened while exploring (a leaf landing on its own family)
            del self.trees[fid]
            del self.fleaves[fid]
            if fid not in todo:
                todo.append(fid)
        elif fid not in self.trees and fid not in todo:
            todo.append(fid)


class AExplorer(T.Explorer):
    """the concrete pass: follow the run leaf by leaf from the boot, exploring
    (TI-style, generically) only the families the run reaches, and record the
    exponents it meets in each"""

    def fam_of(self, q, h, L, R):
        L = T.generalize(L)
        R = T.generalize(R)
        key = (q, h, T.shape(L), T.shape(R))
        ex = T.exps(L) + T.exps(R)
        if key not in self.fidx:
            self.fidx[key] = len(self.fams)
            F = T.Fam(key, [e[0] for e in ex])
            F.seen = False
            self.fams.append(F)
        return self.fidx[key], ex, False

    def run(self, boot, nsteps):
        q, L, h, R = boot
        fid, ex, _ = self.fam_of(q, h, L, R)
        exps = [e[0] for e in ex]
        obs = {}
        for _ in range(nsteps):
            F = self.fams[fid]
            if not F.seen:
                F.lb = list(exps)
                F.seen = True
            elif any(e < l for e, l in zip(exps, F.lb)):
                F.lb = [min(e, l) for e, l in zip(exps, F.lb)]
                self.trees.pop(fid, None)
                self.fleaves.pop(fid, None)
            obs.setdefault(F.key, []).append(list(exps))
            if fid not in self.trees:
                self.explore_fam(fid, [])
                if fid not in self.trees:
                    raise T.Fail('concrete pass: family %d unstable' % fid)
            nodes = self.trees[fid]
            x = [e - l for e, l in zip(exps, F.lb)]
            r = C.twalk(nodes, len(nodes), 0, [(1, 0)] * F.n, x)
            if r is None:
                raise T.Fail('concrete pass: no leaf')
            lf = self.fleaves[fid][r[0]]
            z = r[2]
            exps = [C.aeval(z, e) for e in lf['ex']]
            fid = lf['g']
        seeds = {}
        for key, vs in obs.items():
            c = [min(v[k] for v in vs) for k in range(len(vs[0]))]
            g = [0] * len(c)
            for v in vs:
                for k in range(len(c)):
                    g[k] = math.gcd(g[k], v[k] - c[k])
            seeds[key] = (c, g)
        return seeds


def seed_pass(tab, pins, boot):
    X = AExplorer(tab, pins)
    mf = T.MAXFAM
    T.MAXFAM = 10 ** 6
    try:
        return X.run(boot, ASTEPS)
    finally:
        T.MAXFAM = mf


def assemble(X, t0, mir, pins):
    leaves = []
    fams = []
    for f in range(len(X.fams)):
        if f not in X.fleaves:
            raise T.Fail('unexplored family %d' % f)
    for f in range(len(X.fams)):
        F = X.fams[f]
        base = len(leaves)
        for lf in X.fleaves[f]:
            G = X.fams[lf['g']]
            tgt = G.value(lf['ex'])
            leaves.append(dict(f=f, reg=lf['reg'], g=lf['g'], tgt=tgt, c0=lf['c0'], j=lf['j'],
                               el=lf['el'], er=lf['er'], nL=lf['nL'], nR=lf['nR'],
                               chain=lf['chain']))
        nodes = [(('leaf', base + nd[1]) if nd[0] == 'leaf' else nd) for nd in X.trees[f]]
        pat = F.pattern()
        fams.append(dict(q=F.q, h=F.h, L=pat[0], R=pat[1], n=F.n, tree=nodes))
    f0, ex0 = X.boot
    v0 = [e[0] for e in X.fams[f0].value(ex0)]
    return dict(pins=sorted(pins), fams=fams, leaves=leaves, t0=t0, f0=f0, v0=v0, mir=mir)


GLIST = (0, 1)
TLIST = (3000, 12000, 50000)


def find_dir(tab, mir, qh=False, lastq=0, t0=None):
    """find_dir1 at each boot time in TLIST and each start lattice step G0 in
    GLIST, the first success"""
    global G0
    errs = []
    for tb, g0 in [(tb, g0) for tb in TLIST for g0 in GLIST]:
        G0 = g0
        try:
            r = find_dir1(tab, mir, qh, lastq, tb)
        except T.Fail as e:
            r = dict(err=str(e))
        except RecursionError:
            r = dict(err='recursion')
        if 'err' not in r:
            return r
        errs.append('t%d g%d %s' % (tb, g0, r['err']))
    return dict(err='; '.join(errs))


def find_dir1(tab, mir, qh=False, lastq=0, t0=None):
    """ti_batch.find_dir with the concrete seed pass before the exploration"""
    global SEEDS
    t0 = T.T0 if t0 is None else t0
    if qh:
        pins = T.quiet_pins(tab, lastq)
        if pins is None:
            return dict(err='halts')
        t0 = max(lastq + 64, min(t0, T.QH_BOOT_CAP))
        if t0 > T.QH_BOOT_CAP:
            return dict(err='quiet point past the boot cap')
        r = T.run_conc(tab, t0)
    else:
        r2 = T.run_conc(tab, 60000)
        if r2 is None:
            return dict(err='halts')
        pins = set(k for k in tab if k not in r2[4])
        r = T.run_conc(tab, t0)
    if r is None:
        return dict(err='halts')
    q, L, h, R, fired = r
    boot = (q, C.nstrip(C.norm([('L', L)])), h, C.nstrip(C.norm([('L', R)])))
    tabw = {k: (None if k in pins else v) for k, v in tab.items()}
    try:
        SEEDS = seed_pass(tabw, pins, boot)
    except (T.Fail, T.Req, RecursionError):
        SEEDS = {}
    X = LExplorer(tab, pins)
    X.explore(boot)
    cert = assemble(X, t0, mir, pins)
    cert['qh'] = qh
    err = T.fams_ok(tabw, cert)
    if err:
        return dict(err='fams: ' + err)
    if not T.boot_ok(cert, tab):
        return dict(err='boot')
    fired = [set(C.leaf_fired(tabw, dict(chain=lf['chain'], el=lf['el'], er=lf['er'],
                                         c0=lf['c0']))) for lf in cert['leaves']]
    last = None
    for P in T.PLIST:
        lv = T.live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = T.live_ok(cert, tabw, fired)
            if err:
                return dict(err='live: ' + err)
            if T.nodeidx(cert, [(l, tuple(r)) for l, r in cert['S']], cert['P'], cert['f0'],
                         cert['v0']) is None:
                return dict(err='boot node')
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


def install():
    """route ti_batch's find through the lattice explorer"""
    T.Explorer = LExplorer
    T.assemble = assemble
    T.find_dir = find_dir


def main():
    install()
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('find')
    f.add_argument('rows')
    f.add_argument('out')
    f.add_argument('--jobs', type=int, default=4)
    f.add_argument('--timeout', type=int, default=120)
    f.add_argument('--maxfam', type=int, default=T.MAXFAM)
    f.add_argument('--maxleaf', type=int, default=T.MAXLEAF)
    f.add_argument('--maxsteps', type=int, default=T.MAXSTEPS)
    f.add_argument('--maxna', type=int, default=T.MAXNA)
    f.add_argument('--t0', type=int, default=T.T0)
    f.add_argument('--plist', default=','.join(map(str, T.PLIST)))
    f.add_argument('--force', type=int, default=0)
    b = sub.add_parser('batch')
    b.add_argument('found', nargs='+')
    b.add_argument('--tag', required=True)
    b.add_argument('--chunk', type=int, default=20)
    b.add_argument('--skip', action='append', default=[])
    b.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    if a.cmd == 'find':
        T.cmd_find(a)
    else:
        T.cmd_batch(a)


if __name__ == '__main__':
    main()
