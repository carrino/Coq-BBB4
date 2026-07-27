#!/usr/bin/env python3
"""UNTRUSTED Stage-C probe, second generation: enumerate inner keys, and try
the [lift] route.

`nestboot.py` (wave-15) measured the nested-lap boot chain at 1 of 12 and the
exit chain at 4 of 12, and `docs/NESTED_LAP_PLAN.md` records two reasons the
number should be higher, neither of which that prototype implements:

  1. **Key enumeration.**  `innerfam` reports the BEST-SCORING inner key; a
     machine has 16-27 keys that decode consecutively and the one the boot can
     land on is never the best-scoring one.  Ranking must be replaced by
     enumeration (the wave-13 section 4.1 lesson).

  2. **The [lift] route.**  `nestboot.py` predates wave-16, so it calls
     `derive_chain` with the default `lift=False` -- the acceptance test that
     wave-16 measured to be STRICTER THAN THE THEOREM.  The symptom recorded
     for the boot is the same one wave-16 found on the interior branch: the
     chain lands one or two trailing blanks past the anchor
     (`NESTED_LAP_PLAN.md`: real inner anchor `L=11111111100`, symbolic
     `rep [1,1] 4 ++ [1]`, "9 cells, real is 11").

This probe runs the 2x2: {best key, every key} x {lift=False, lift=True}, so
the two effects are separated rather than confounded.

Usage:
    nestboot2.py LISTFILE [--json OUT] [-K 6] [--keys N] [--limit N]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.chdir(os.path.dirname(os.path.dirname(HERE)) if False else
         os.path.abspath(os.path.join(HERE, '..', '..')))

import emit_lapcert as EL                                          # noqa: E402
import innerfam as IF                                              # noqa: E402
import lapcert as LC                                               # noqa: E402
from emit_interleave import parse                                  # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402

LAB = 'ABCD'
ELER = ((True, True), (False, True), (True, False))


def endpoints(r, key, name_in):
    """The four symbolic endpoints of the nested overflow branch.

    outer all-ones  B0out = rep uS_out (j+obS) ++ soS_out ++ tail_out
    inner start     CinS  = rep uD_in  j       ++ soD_in  ++ tail_in
    inner fill      CinF  = rep uS_in  j       ++ soD_in  ++ tail_in
    outer successor B1out = rep uD_out (S j)   ++ soD_out ++ tail_out
    """
    _, st_in, tail_in, far_in = key
    dout, din = EL.ENCDATA[r['enc']], EL.ENCDATA[name_in]
    st_out = LAB.index(r['st0'])
    tail_out, far_out = tuple(r['tail']), tuple(r['far'])
    Fout = (far_out, (), 0, 0, ())
    Fin = (tuple(far_in), (), 0, 0, ())
    ob = dout['obS']
    if ob >= 1:
        B0out = (st_out, (dout['uS'], dout['uS'], 1, ob - 1,
                          dout['soS'] + tail_out), 0, Fout)
    else:
        B0out = (st_out, ((), dout['uS'], 1, 0, dout['soS'] + tail_out), 0, Fout)
    B1out = (st_out, ((), dout['uD'], 1, 1, dout['soD'] + tail_out), 0, Fout)
    ti = tuple(tail_in)
    CinS = (st_in, ((), din['uD'], 1, 0, din['soD'] + ti), 0, Fin)
    CinF = (st_in, ((), din['uS'], 1, 0, din['soD'] + ti), 0, Fin)
    return B0out, CinS, CinF, B1out


def inner_interior(key, name_in):
    """The INNER family's own INTERIOR lap endpoints -- [NestedLap.Hin].

    Same shape as `emit_lapcert.confs`'s A0/A1: the high-order digits are
    OPAQUE (el = False), so the anchor's tail never appears.
    """
    _, st_in, _, far_in = key
    d = EL.ENCDATA[name_in]
    F = (tuple(far_in), (), 0, 0, ())
    A0 = (st_in, ((), d['uS'], 1, 0, d['sS']), 0, F)
    A1 = (st_in, ((), d['uD'], 1, 0, d['sD']), 0, F)
    return A0, A1


def chain(tab, a, b, lift, elers=ELER):
    """First (el, er) at which a chain a -> b derives.  None if none does."""
    for (el, er) in elers:
        try:
            ch = LC.derive_chain(tab, el, er, a, b, lift=lift)
        except Exception:                                          # noqa: BLE001
            ch = None
        if ch is not None:
            return dict(len=len(ch), el=el, er=er, chain=[list(s) for s in ch])
    return None


def try_machine(spec, K=6, maxkeys=40, grid=True):
    r = IF.phase_probe(spec, K=K)
    if r is None:
        return None
    keys = [i for i in r['inner'] if i['kind'].startswith('EXACT')]
    if not keys:
        return dict(spec=spec, why='inner not at pow2 j (octave/offset)',
                    nkeys=len(r['inner']))
    tab = parse(spec)
    out = dict(spec=spec, outer=r['enc'], st_out=r['st0'],
               tail_out=list(r['tail']), far_out=list(r['far']),
               nkeys=len(keys), cells={})
    # 2x2: {best key only, every key} x {lift False, True}
    cases = ((False, 'best'), (False, 'all'), (True, 'best'), (True, 'all')) \
        if grid else ((True, 'all'),)
    for lift, scope in cases:
        ks = keys[:1] if scope == 'best' else keys[:maxkeys]
        got = None
        for i in ks:
            name_in = i['key'][0]
            B0out, CinS, CinF, B1out = endpoints(r, i['key'], name_in)
            boot = chain(tab, B0out, CinS, lift)
            if boot is None:
                continue
            exit_ = chain(tab, CinF, B1out, lift)
            A0i, A1i = inner_interior(i['key'], name_in)
            ilap = chain(tab, A0i, A1i, False, ((False, True),)) \
                or chain(tab, A0i, A1i, True, ((False, True),))
            cand = dict(inner=name_in, st_in=LAB[i['key'][1]],
                        tail_in=list(i['key'][2]), far_in=list(i['key'][3]),
                        boot=boot, exit=exit_, ilap=ilap)
            if got is None or (exit_ is not None and got['exit'] is None) \
               or (exit_ is not None and ilap is not None):
                got = cand
            if exit_ is not None and ilap is not None:
                break
        out['cells']['%s/lift=%s' % (scope, lift)] = got
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('list')
    ap.add_argument('--json')
    ap.add_argument('-K', type=int, default=6)
    ap.add_argument('--keys', type=int, default=40)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--no-grid', action='store_true',
                    help='only the all-keys/lift=True cell (the fast survey)')
    a = ap.parse_args()
    specs = [l.strip() for l in open(a.list) if l.strip()]
    if a.limit:
        specs = specs[:a.limit]

    rows, tally = [], {}
    for n, spec0 in enumerate(specs):
        got = None
        for s in (spec0, mirror_spec(spec0)):
            try:
                got = try_machine(s, a.K, a.keys, not a.no_grid)
            except Exception as e:                                 # noqa: BLE001
                got = dict(spec=s, why='ERR %s' % e)
            if got and got.get('cells'):
                break
        rows.append(got)
        if not got or not got.get('cells'):
            print('%4d/%d %-42s  %s' % (n + 1, len(specs), spec0,
                                        (got or {}).get('why', 'NO-INNER')),
                  flush=True)
            continue
        marks = []
        for cell, v in got['cells'].items():
            if v is None:
                tag = '-'
            else:
                tag = 'B' + ('E' if v['exit'] else '') \
                          + ('I' if v['ilap'] else '')
            tally[cell + ':' + tag] = tally.get(cell + ':' + tag, 0) + 1
            marks.append('%s=%s' % (cell, tag))
        print('%4d/%d %-42s out=%-14s keys=%-3d %s'
              % (n + 1, len(specs), spec0, '%s@%s' % (got['outer'],
                 got['st_out']), got['nkeys'], '  '.join(marks)), flush=True)

    print('\n=== boot(B) / boot+exit(BE) per cell, over %d machines ===' %
          len(specs))
    for k in sorted(tally):
        print('%5d  %s' % (tally[k], k))
    if a.json:
        json.dump(rows, open(a.json, 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
