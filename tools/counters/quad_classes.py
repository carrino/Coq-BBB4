#!/usr/bin/env python3
"""UNTRUSTED: what the QUAD emitter's four measured extensions actually need.

WAVE27 section 3 boarded 6 of the 41 `QUAD`/`QUAD` rows and named the rest by
size: 16 parity-class, 12 double-ladder, 4 non-rep right sides, 3 deep-pivot.
`quad_emit.extract` refuses each of them at a DIFFERENT gate, and the four
gates are not equally deep -- the parity one is templating (the law is
already measured per class, the emitter just renders one), the double-ladder
one is a reader change.

This scan runs `quad_probe.read_law` over a list and reports, per row, the
gate that fires and the per-class shape behind it:

    classes   micro/term/ovf/bootint/bootovf  -- how many k-parity classes
              each law needs.  All 1 is the boarded shape; 2 is the parity
              extension, and it is the SAME 2 everywhere or it is not one
              reindex.
    marks     the (nint, novf) mark-count law; anything but (1,1)/(1,2) is
              a ladder the plain reader does not walk.
    mode      (-1, False) is the boarded pivot; (1, True) is deep-pivot.
    stride    len(uS); 2 is the non-rep right side.

Usage
  quad_classes.py --list FILE [--json OUT]
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import quad_probe as QP                                            # noqa: E402
import emit_lapcert as EL                                          # noqa: E402

CLS = ('micro', 'term', 'ovf', 'bootint', 'bootovf')


def probe(spec):
    try:
        law = QP.read_law(spec)
    except Exception as e:                                         # noqa: BLE001
        return dict(spec=spec, ok=False, why='%s: %s' % (type(e).__name__, e))
    A = law['anchor']
    d = EL.ENCDATA[A['enc']]
    cls = {c: len(law.get(c) or []) for c in CLS}
    r = dict(spec=spec, ok=True, enc=A['enc'], mode=list(law['mode']),
             classes=cls, stride=len(d['uS']),
             nint=list(law['nint']), novf=list(law['novf']))
    if law['mode'] != (-1, False):
        r['gate'] = 'deep-pivot'
    elif len(d['uS']) != 1:
        r['gate'] = 'stride-%d' % len(d['uS'])
    elif any(v != 1 for v in cls.values()):
        n = sorted({v for v in cls.values() if v != 1})
        r['gate'] = ('parity' if n == [2] else 'classes-%s' %
                     ','.join(map(str, n)))
    elif law['nint'] != (1, 1) or law['novf'] != (1, 2):
        r['gate'] = 'ladder'
    else:
        r['gate'] = 'boarded-shape'
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    cnt, res = collections.Counter(), []
    for i, spec in enumerate(specs):
        r = probe(spec)
        res.append(r)
        cnt[r.get('gate') or 'read-failed'] += 1
        print('%4d/%d %-40s %-14s %s' % (
            i + 1, len(specs), spec, r.get('gate') or 'READ-FAILED',
            ('%s mode=%s stride=%d cls=%s n=%s/%s'
             % (r['enc'], r['mode'], r['stride'],
                ''.join(str(r['classes'][c]) for c in CLS),
                r['nint'], r['novf'])) if r['ok'] else r['why'][:70]),
            flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
