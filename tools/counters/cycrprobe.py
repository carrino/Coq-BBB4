#!/usr/bin/env python3
"""UNTRUSTED diagnostic: DUMP the dead-end configurations of the `cycR-gap`
rows, so the new primitive is read OFF THE MACHINE rather than guessed.

`intgap.py` counts dead ends whose right side still carries the repeated block
and whose left prefix is non-empty (`_cycr_gap`).  A count is not enough to
state a lemma: the arm we are about to add to the trusted checker has to match
what the machine actually leaves on the tape.  This prints, per row and per
framing, the dead end itself, the target, and the three facts the mirrored
`SCycL` arm needs to hold:

  * the RIGHT prefix is empty (mirror of `SCycL`'s `s_pre (c_l c) = []`);
  * the LEFT side carries no block of its own (`s_u (c_l c) = []`);
  * some split `s_pre (c_l c) = lw ++ rest` has a unit run
    `(q, (lw, h, u)) -> (q, (lw ++ w, h, []))` that closes -- which is
    `cycRW` at `rw = []`, i.e. `SCycR2 n m` with `m = length lw`.

Usage
  cycrprobe.py --list FILE [--only-gap] [--out JSON]
  cycrprobe.py --spec SPEC
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
import lapcert as LC                                               # noqa: E402
from emit_interleave import parse, LAB                             # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
import intgap as IG                                                # noqa: E402

SYM = {0: '0', 1: '1'}


def fs(t):
    return ''.join(SYM.get(x, '?') for x in t)


def fside(s):
    pre, u, a, b, post = s
    blk = '' if not u else '[%s]^(%d j + %d)' % (fs(u), a, b)
    return '%s%s%s' % (fs(pre) or '.', blk, fs(post) or '.')


def fconf(c):
    q, L, h, R = c
    return '%s  L=%-28s h=%s  R=%s' % (LAB[q], fside(L), SYM.get(h, '?'),
                                       fside(R))


def unit_runs(tab, c, nmax=64):
    """Every `SCycR2 n m` whose unit run closes at this configuration: split
    the left prefix as `lw ++ rest` and look for a return to the same
    (state, head) with the right block consumed and `lw` restored."""
    q, L, h, R = c
    out = []
    if R[0] or L[1] or not R[1]:
        return out
    for m in range(len(L[0]) + 1):
        lw = L[0][:m]
        cfg = (q, lw, h, R[1])
        for n in range(1, nmax + 1):
            try:
                cfg = LC.wstep(tab, True, True, cfg)
            except LC.Halt:
                break
            if cfg is None:
                break
            q2, l2, h2, r2 = cfg
            if not r2 and q2 == q and h2 == h and l2[:len(lw)] == lw:
                out.append(dict(n=n, m=m, lw=fs(lw), w=fs(l2[len(lw):])))
                break
    return out


def probe(spec):
    for mir in (False, True):
        ds = mirror_spec(spec) if mir else spec
        tab = parse(ds)
        for (edge, tail, p0, enc, far) in EL.anchors(ds):
            d = EL.ENCDATA[enc]
            uS, sS = tuple(d['uS']), tuple(d['sS'])
            uD, sD = tuple(d['uD']), tuple(d['sD'])
            F = (tuple(far), (), 0, 0, ())
            st = LAB.index(edge)
            frames = {
                'one': ((st, ((), uS, 1, 0, sS), 0, F),
                        (st, ((), uD, 1, 0, sD), 0, F)),
                'z': ((st, (sS, (), 0, 0, ()), 0, F),
                      (st, (sD, (), 0, 0, ()), 0, F)),
                'p': ((st, (uS, uS, 1, 0, sS), 0, F),
                      (st, (uD, uD, 1, 0, sD), 0, F)),
            }
            out = dict(spec=spec, mirror=mir, enc=enc, edge=edge,
                       tail=list(tail), far=list(far), frames={})
            for name, (a, b) in frames.items():
                seen, dead = IG._closure(tab, a, b)
                gap = IG._cycr_gap(dead)
                fr = dict(reach=len(seen), dead=len(dead), gap=len(gap),
                          target=fconf(b), ends=[])
                for c in gap:
                    fr['ends'].append(dict(
                        conf=fconf(c),
                        rpre_empty=not c[3][0],
                        lu_empty=not c[1][1],
                        runs=unit_runs(tab, c)))
                out['frames'][name] = fr
            return out
    return dict(spec=spec, verdict='no anchor family')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    ap.add_argument('--only-gap', action='store_true')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, cnt = [], collections.Counter()
    for spec in specs:
        r = probe(spec)
        ends = sum(len(f['ends']) for f in r.get('frames', {}).values())
        runs = sum(len(e['runs']) for f in r.get('frames', {}).values()
                   for e in f['ends'])
        if a.only_gap and not ends:
            continue
        res.append(r)
        cnt['rows'] += 1
        cnt['with dead end'] += bool(ends)
        cnt['with a closing unit run'] += bool(runs)
        print('== %s  %s@%s tail=%s far=%s%s' % (
            spec, r.get('enc'), r.get('edge'), fs(r.get('tail', ())) or '.',
            fs(r.get('far', ())) or '.', '  MIRRORED' if r.get('mirror') else ''))
        for name, f in r.get('frames', {}).items():
            if not f['ends']:
                continue
            print('   %-4s reach=%-3d dead=%d' % (name, f['reach'], f['dead']))
            print('        target   %s' % f['target'])
            for e in f['ends']:
                print('        deadend  %s' % e['conf'])
                print('                 rpre_empty=%s lu_empty=%s'
                      % (e['rpre_empty'], e['lu_empty']))
                for u in e['runs']:
                    print('                 SCycR2 n=%d m=%d  lw=%s -> w=%s'
                          % (u['n'], u['m'], u['lw'] or '.', u['w'] or '.'))
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
