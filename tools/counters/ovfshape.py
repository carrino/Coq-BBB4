#!/usr/bin/env python3
"""UNTRUSTED: measure the OVERFLOW lap's cost as a function of the carry index.

WAVE13_FINDINGS.md section 9c measured the INTERIOR lap's cost-vs-j and found
a quadratic family that five waves of chain-search widening could not possibly
have reached.  The same measurement was never made for the OVERFLOW branch --
the branch that section 10a measures as the binding constraint for ~523
machines.  This makes it.

Both branches are classified by finite differences of the lap cost:

    AFFINE         d1 constant                 -- inside the certificate model
    PARITY-AFFINE  affine on each parity of j  -- IN model after re-indexing
                                                  j = 2i+r (section 9b)
    QUAD           d2 constant                 -- outside it (section 9c)
    EXP2/3/4       d2 scales by 2 / 3 / 4      -- outside it, c*b^j + a*j + b
    HIGHER         none of the above

[srun] returns a step count [ca*j + cb] and [sside] carries its count as
[a*j + b], so ONLY AFFINE is expressible.  A machine whose overflow is EXP2 is
not one chain away from a board; it is one INDUCTION LEVEL away, which is what
Counters/IXPGadgets.v provides for the family wave-12 boarded by hand.

The anchor is taken from emit_lapcert's own search (mirror included), so the
verdict is about the branch the emitter actually tries, not a hand-picked one.
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_interleave import parse, ENC, LAB, carry                 # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
import lapcert as LC                                               # noqa: E402


def anchor_times(spec, st0, encf, tail, far, pmax, T):
    """t(p) = first time the run is at the anchor Cc p, for p = 1..pmax."""
    # the anchor tail may carry trailing blanks, which [lift] cannot see and
    # the concrete tape does not store -- compare both sides stripped
    tail, far = tuple(tail), LC.rstrip0(tuple(far))
    want = {}
    for p in range(1, pmax + 1):
        want[(st0, LC.rstrip0(tuple(encf(p)) + tail), far)] = p
    tab = parse(spec)
    cfg = (0, (), 0, ())
    out = {}
    for t in range(T):
        q, l, h, r = cfg
        if h == 0:
            p = want.get((q, LC.rstrip0(l), LC.rstrip0(r)))
            if p is not None and p not in out:
                out[p] = t
                if len(out) == pmax:
                    break
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def degree(pts):
    """pts = [(j, cost)] at CONSECUTIVE j.  Classify by finite differences."""
    if len(pts) < 4:
        return 'few', None
    js = [j for j, _ in pts]
    if js != list(range(js[0], js[0] + len(js))):
        return 'gappy', None
    c = [v for _, v in pts]
    d1 = [c[i + 1] - c[i] for i in range(len(c) - 1)]
    if len(set(d1)) == 1:
        return 'AFFINE', (0, d1[0], c[0] - js[0] * d1[0])
    d2 = [d1[i + 1] - d1[i] for i in range(len(d1) - 1)]
    if len(set(d2)) == 1:
        return 'QUAD', None
    if len(d2) >= 3 and all(x > 0 for x in d2):
        for base, name in ((2, 'EXP2'), (4, 'EXP4'), (3, 'EXP3')):
            if all(d2[i + 1] == base * d2[i] for i in range(len(d2) - 1)):
                return name, None
    # affine on each PARITY class of j: wave-13 section 9b's two-pass carry,
    # where the traversal period is 2 CELLS while the block unit is 1.  The
    # existing checker expresses this after re-indexing j = 2i + r, so these
    # are IN-model and should not be filed with the exponentials.
    ev = [(j, v) for j, v in pts if j % 2 == 0]
    od = [(j, v) for j, v in pts if j % 2 == 1]

    def _aff(q):
        if len(q) < 3:
            return False
        d = [q[i + 1][1] - q[i][1] for i in range(len(q) - 1)]
        return len(set(d)) == 1

    if _aff(ev) and _aff(od):
        return 'PARITY-AFFINE', None
    return 'HIGHER', None


def measure(spec, dspec, edge, tail, p0, enc, far, pmax, T):
    st0 = LAB.index(edge)
    encf = ENC[enc]
    at = anchor_times(dspec, st0, encf, tail, far, pmax, T)
    lap = {p: at[p + 1] - at[p] for p in sorted(at)
           if p + 1 in at and at[p + 1] > at[p]}
    ic, oc = {}, {}
    for p, n in lap.items():
        j, ov = carry(p)
        (oc if ov else ic).setdefault(j, set()).add(n)
    ipts = [(j, next(iter(v))) for j, v in sorted(ic.items())
            if len(v) == 1 and j <= 9]
    opts = [(j, next(iter(v))) for j, v in sorted(oc.items())
            if len(v) == 1 and j <= 12]
    idg, ifit = degree(ipts)
    odg, ofit = degree(opts)
    return dict(spec=spec, enc=enc, edge=edge, tail=list(tail),
                far=list(far), interior=idg, overflow=odg,
                ipts=ipts[:10], opts=opts[:12],
                ifit=ifit, ofit=ofit, n=len(at))


def classify(spec, pmax=520, T=4000000):
    """The FIRST anchor emit_lapcert would try, direct then mirrored."""
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in EL.anchors(dspec):
            try:
                r = measure(spec, dspec, edge, tail, p0, enc, far, pmax, T)
            except Exception:                                     # noqa: BLE001
                continue
            if r['overflow'] not in ('few', 'gappy'):
                r['mirror'] = mirrored
                return r
    return dict(spec=spec, interior='-', overflow='no-anchor', enc=None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--pmax', type=int, default=520)
    ap.add_argument('-T', type=int, default=4000000)
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [l.strip() for l in open(a.list) if l.strip()])
    if a.limit:
        specs = specs[:a.limit]
    c, out = collections.Counter(), []
    for i, s in enumerate(specs):
        r = classify(s, a.pmax, a.T)
        k = '%s/%s' % (r['interior'], r['overflow'])
        c[k] += 1
        out.append(r)
        print('%5d/%d %-40s int=%-7s ovf=%-7s %s'
              % (i + 1, len(specs), s, r['interior'], r['overflow'],
                 r.get('enc') or '-'), flush=True)
        if a.v and r.get('opts'):
            print('        interior %s' % r['ipts'])
            print('        overflow %s' % r['opts'])
    print('\n=== interior/overflow degree ===')
    for k, v in c.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(out, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
