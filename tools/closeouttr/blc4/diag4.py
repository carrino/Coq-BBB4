#!/usr/bin/env python3
"""BLC4 diagnostic (UNTRUSTED): which explored families does the REAL run
never visit?  Runs lg_batch's concrete data pass (the real run, leaf by
leaf, through the same fam_of) from the boot, then the exploration, and
prints the first explored families whose key the real run never produced,
with the family whose leaf created them.

    python3 tools/closeouttr/blc4/diag4.py SPEC [NLEAVES] [MAXFAM]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import learn4 as L                                   # noqa: E402
import lg4                                           # noqa: E402
import lg3                                           # noqa: E402
import lg_batch as G                                 # noqa: E402
import ti_batch as T                                 # noqa: E402


def main():
    spec = sys.argv[1]
    nl = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    G.MAXFAM = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    lang, mir, info = L.learn(spec)
    t0 = info.get('tboot') or 20000
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    pins = set(k for k in tab if k not in r2[4])
    lg4.CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
    Xr = lg4.X4(tab, pins, lang)
    boot = lg3.boot_of(Xr, tab, t0)
    try:
        Xr.data_pass(boot, nl)
    except T.Fail as e:
        print('data pass stopped:', e)
    real = set(Xr.fidx)
    print('real run: %d families' % len(real))
    Xe = lg4.X4(tab, pins, lang)
    parent = {}
    orig = Xe.explore_fam
    cur = [None]

    def ef(fid, todo):
        cur[0] = fid
        return orig(fid, todo)
    Xe.explore_fam = ef
    of = Xe.fam_of

    def fo(*a, **k):
        n0 = len(Xe.fams)
        r = of(*a, **k)
        if len(Xe.fams) > n0:
            parent[r[0]] = cur[0]
        return r
    Xe.fam_of = fo
    boot = lg3.boot_of(Xe, tab, t0)
    try:
        Xe.explore(boot)
        print('exploration closes')
    except T.Fail as e:
        print('exploration:', e)
    bad = [i for i, F in enumerate(Xe.fams) if F.key not in real]
    print('%d of %d explored families the real run never visits' % (len(bad), len(Xe.fams)))
    for i in bad[:int(os.environ.get('DIAG_N', '12'))]:
        p = parent.get(i)
        print('  %d %s' % (i, lg3.fmt_key(Xe.fams[i].key)[:200]))
        if p is not None:
            print('     <- %d %s%s' % (p, lg3.fmt_key(Xe.fams[p].key)[:180],
                                    '' if Xe.fams[p].key in real else '  (also unreal)'))


if __name__ == '__main__':
    main()


def show_real(spec, nl=3000, pat=''):
    lang, mir, info = L.learn(spec)
    t0 = info.get('tboot') or 20000
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    pins = set(k for k in tab if k not in r2[4])
    Xr = lg4.X4(tab, pins, lang)
    boot = lg3.boot_of(Xr, tab, t0)
    try:
        Xr.data_pass(boot, nl)
    except T.Fail as e:
        print('data pass stopped:', e)
    for i, F in enumerate(Xr.fams):
        k = lg3.fmt_key(F.key)
        if pat in k:
            print(i, k[:220], F.hull.base)
