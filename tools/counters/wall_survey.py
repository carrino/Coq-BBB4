#!/usr/bin/env python3
"""UNTRUSTED survey: bucket the residue by WHICH PART of the certificate fails.

emit_lapcert.process() reports only the last failure it saw across every
(mirror, anchor) candidate, which conflates "no anchor at all" with "anchor
fine, overflow chain missing".  This walks the same candidates and records,
per machine, the BEST outcome reached -- so the buckets of WAVE13_FINDINGS.md
section 10a can be recomputed exactly and re-measured after a change.

Stages, in order of progress:
  no-anchor < no-interior < no-overflow < novis < other < OK
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_interleave import DeriveError                            # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
import lapcert as LC                                               # noqa: E402

RANK = {'no-anchor': 0, 'no-interior': 1, 'no-overflow': 2, 'novis': 3,
        'other': 4, 'OK': 5}


def bucket(msg):
    if 'no interior chain' in msg:
        return 'no-interior'
    if 'no overflow chain' in msg or 'overflow close' in msg:
        return 'no-overflow'
    if 'no visit witness' in msg:
        return 'novis'
    return 'other'


def survey_one(spec):
    best, why, tag = 'no-anchor', 'no anchor', None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in EL.anchors(dspec):
            if RANK[best] < RANK['no-interior']:
                best, why = 'no-interior', 'anchor only'
            try:
                EL.derive(dspec, edge, tail, p0, enc, far)
                return 'OK', enc + ('/mirror' if mirrored else ''), ''
            except (DeriveError, LC.Halt) as e:
                b = bucket(str(e))
                if RANK[b] > RANK[best]:
                    best, why = b, str(e)[:80]
                    tag = enc + ('/mirror' if mirrored else '')
            except Exception as e:                                # noqa: BLE001
                if RANK['other'] > RANK[best]:
                    best, why = 'other', '%s: %s' % (type(e).__name__, e)[:80]
    return best, tag, why


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--offset', type=int, default=0)
    a = ap.parse_args()
    specs = [l.strip() for l in open(a.list) if l.strip()]
    specs = specs[a.offset:]
    if a.limit:
        specs = specs[:a.limit]
    c, out = collections.Counter(), []
    for i, s in enumerate(specs):
        try:
            b, tag, why = survey_one(s)
        except Exception as e:                                    # noqa: BLE001
            b, tag, why = 'other', None, '%s: %s' % (type(e).__name__, e)
        c[b] += 1
        out.append(dict(spec=s, bucket=b, enc=tag, why=why))
        print('%5d/%d %-40s %-12s %-10s %s'
              % (i + 1, len(specs), s, b, tag or '-', why[:60]), flush=True)
    print('\n=== buckets ===')
    for k, v in c.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(out, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
