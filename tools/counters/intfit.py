#!/usr/bin/env python3
"""UNTRUSTED probe: is the two-form INTERIOR lap's step count affine in [j]?

40 rows are filed `no interior j=S j chain at octave parity 0` -- the largest
single bucket in the (4,2) residue, and no wave has written an item for it.
Before any framing is designed for it, the first question is whether a chain of
ANY depth can express the lap at all: `srun`'s cost is `a * j + b`, so a lap
whose measured cost is not affine in [j] is not a framing problem.

WAVE29 section 7 is the trap this probe is built around: a period-P frame makes
a SINGLE affine fit report "exponential" on branches that are really `4k+7` and
`4k+9` per parity.  So the fit is reported PER OCTAVE CLASS and, before that,
the probe checks whether the cost is a function of `(parity, j)` at all -- if it
also depends on the octave [k], the residue is not one law with noise, it is
several laws, and the report says so.

Everything is measured against the raw simulator: no chain is derived and no
certificate is written.

Usage
  intfit.py --list FILE [--json OUT] [--hi N]
  intfit.py --spec SPEC
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
import lapcert as LC                                               # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse, carry                           # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, octave                               # noqa: E402

MAXSTEP = 4000000


def laps(spec, hi=512):
    """Every INTERIOR lap of [spec]'s two-form family, measured: the exact
    number of raw steps from the anchor at [p] to the anchor at [p + 1], for
    every [p] whose [cview] is not the overflow shape."""
    last = None
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        try:
            tab = parse(dspec)
            enc, frames, ks = TC.two_form(dspec, None)
        except RegError as e:
            last = str(e)
            continue
        st = {b: frames[b][0] for b in (0, 1)}
        tl = {b: tuple(frames[b][1]) for b in (0, 1)}
        fr = {b: tuple(frames[b][2]) for b in (0, 1)}
        encf = ENC[enc]

        def anchor(p):
            b = octave(p) % 2
            return (st[b], tuple(encf(p)) + tl[b], 0, fr[b])

        out = []
        for p in range(1 << ks[0], hi):
            if octave(p + 1) > ks[-1]:
                break
            j, ov = carry(p)
            if ov:
                continue
            cfg, want, n = anchor(p), anchor(p + 1), 0
            while n < MAXSTEP:
                cfg = LC.wstep(tab, False, False, cfg)
                n += 1
                if EL.eqlift(cfg, want):
                    break
            else:
                n = None
            out.append(dict(p=p, k=octave(p), b=octave(p) % 2, j=j, n=n))
        return dict(spec=spec, dspec=dspec, mirror=mir, enc=enc, ks=ks,
                    laps=out)
    raise RegError(last or 'no family')


def fit(rows):
    """(a, b) with n = a*j + b over [rows], or None when no affine law fits."""
    pts = sorted({(r['j'], r['n']) for r in rows if r['n'] is not None})
    if len(pts) < 2:
        return (0, pts[0][1]) if len(pts) == 1 and pts[0][0] == 0 else None
    (j0, n0), (j1, n1) = pts[0], pts[-1]
    if j1 == j0 or (n1 - n0) % (j1 - j0):
        return None
    a = (n1 - n0) // (j1 - j0)
    b = n0 - a * j0
    return (a, b) if all(n == a * j + b for j, n in pts) else None


def classify(D):
    """Per octave parity: is the cost a FUNCTION of (parity, j), and if so is
    it affine?  Reports the split by octave when it is not."""
    out = {}
    for b in (0, 1):
        rows = [r for r in D['laps'] if r['b'] == b]
        if not rows:
            out[b] = dict(verdict='no anchors')
            continue
        if any(r['n'] is None for r in rows):
            out[b] = dict(verdict='does not close within %d steps' % MAXSTEP)
            continue
        byj = {}
        for r in rows:
            byj.setdefault(r['j'], set()).add(r['n'])
        multi = {j: sorted(v) for j, v in byj.items() if len(v) > 1}
        if multi:
            # not a function of (parity, j): report the per-octave laws, which
            # is the WAVE29 section 7 shape.
            per = {}
            for k in sorted({r['k'] for r in rows}):
                per[k] = fit([r for r in rows if r['k'] == k])
            out[b] = dict(verdict='not a function of (parity, j)',
                          clash={str(j): v for j, v in sorted(multi.items())},
                          per_octave={str(k): v for k, v in per.items()},
                          affine_per_octave=all(v is not None
                                                for v in per.values()))
            continue
        f = fit(rows)
        # the j = 0 half is a separate branch in `_derive`; fit the peeled half
        # (j >= 1) on its own too, since that is the one that is failing.
        fp = fit([r for r in rows if r['j'] >= 1])
        out[b] = dict(verdict='affine' if f else ('affine on j>=1' if fp
                                                 else 'not affine'),
                      law=f, law_j1=fp,
                      pts=sorted({(r['j'], r['n']) for r in rows}))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('--hi', type=int, default=512)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.split()[0] for x in open(a.list) if x.strip()
              and not x.startswith('#')])
    out, tally = [], {}
    for i, s in enumerate(specs):
        try:
            D = laps(s, a.hi)
        except Exception as e:                                      # noqa: BLE001
            print('%4d/%d %-30s NO: %s' % (i + 1, len(specs), s, e))
            tally['probe failed'] = tally.get('probe failed', 0) + 1
            continue
        C = classify(D)
        D['cls'] = C
        out.append(D)
        for b in (0, 1):
            v = C[b]['verdict']
            tally['b%d %s' % (b, v)] = tally.get('b%d %s' % (b, v), 0) + 1
        print('%4d/%d %-30s %-14s b0 %-28s b1 %-28s'
              % (i + 1, len(specs), s, D['enc'],
                 _law(C[0]), _law(C[1])))
    print('\n--- tally ---')
    for k in sorted(tally):
        print('%5d  %s' % (tally[k], k))
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


def _law(c):
    v = c['verdict']
    if v == 'affine':
        return '%d*j+%d' % c['law']
    if v == 'affine on j>=1':
        return 'j>=1: %d*j+%d' % c['law_j1']
    if v == 'not a function of (parity, j)':
        return 'per-octave%s' % (' (all affine)' if c['affine_per_octave']
                                 else ' (NOT affine)')
    return v


if __name__ == '__main__':
    sys.exit(main())
