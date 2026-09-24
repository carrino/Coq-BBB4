#!/usr/bin/env python3
"""RepWL finder results -> closeout batches (UNTRUSTED generator).

    python3 tools/closeouttr/rw_batch.py FOUND.json [FOUND2.json ...] --tag RW [--chunk 50]

Takes the `ok` rows of tools/censustr/rw_cert_find.py `find` output (the
never-QH mode) that are still in closeouttr_remaining.txt, and writes
theories/CloseoutTr/CBT_<TAG>_<NN>.v from the next free NN.  Each row is
proved by Coq's own RepWL tier ([RepWLTr.rw_tier_tr_sound]) re-running the
search at the finder's parameters -- no certificate literal is stored.

Compile the batch before committing: a row whose parameters Coq's tier
rejects fails its [vm_cast] (the finder's closure is capped below Coq's, so
this is rare).  Drop such a row with --skip SPEC and regenerate.
Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

REQ = ['From BBB4.CensusTr Require Import RepWLTr.']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='RW')
    ap.add_argument('--chunk', type=int, default=50)
    ap.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.found:
        for r in json.load(open(f)):
            if r.get('ok') and r['spec'] in remaining and r['spec'] not in seen \
                    and r['spec'] not in a.skip:
                seen.add(r['spec'])
                rows.append(r)
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        entries = [(r['spec'],
                    'apply coversTr_nqh, (rw_tier_tr_sound _ %d %d %d %d %d). '
                    'vm_cast_no_check (eq_refl true).' % (r['L'], r['T'], r['t'], r['fuel'], r['M']))
                   for r in rows[i:i + a.chunk]]
        made.append(write_batch(a.tag, nn, REQ, entries,
                                'never-QH by RepWL (rw_tier_tr) at finder parameters'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
