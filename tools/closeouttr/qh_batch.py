#!/usr/bin/env python3
"""Quasihalting RepWL finder results -> closeout batches (UNTRUSTED generator).

    python3 tools/closeouttr/qh_batch.py FOUND.json [...] --tag QH [--chunk 50]

Takes the `ok` rows of tools/censustr/rw_cert_find.py `find --qh` output
that are still in closeouttr_remaining.txt, and writes
theories/CloseoutTr/CBT_<TAG>_<NN>.v from the next free NN.  Each row is
proved by the wrapped RepWL tier through [QHConveyorTr.rwqh_stage]: the
quiet instructions pinned at their last fires, Coq re-running the closure
and the rank search on the wrapped machine, the bound 32779478.

Pin from the 1e8 scan (`--scan censustr_v9_scan_1e8.txt`): a 1e6 pin can
fire again later, and then [rwqh_stage] fails the row soundly -- but it
wastes the run.  Compile the batch before committing; drop a row Coq
rejects with --skip SPEC.  Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'censustr'))
from cbt import REPO, next_free, write_batch  # noqa: E402
from rw_cert_find import coq_lf, fmt_nat  # noqa: E402

REQ = ['From BBB4.CensusTr Require Import TNF_QHTr RepWLTr QHConveyorTr.']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='QH')
    ap.add_argument('--chunk', type=int, default=50)
    ap.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.found:
        for r in json.load(open(f)):
            if r.get('ok') and r.get('qh') and r['spec'] in remaining \
                    and r['spec'] not in seen and r['spec'] not in a.skip:
                seen.add(r['spec'])
                rows.append(r)
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        # M + 8: the same headroom the proven-QH stages give the wrapped tier
        entries = [(r['spec'],
                    'apply coversTr_qh3, (rwqh_stage _ %s %d %d %s %s %d 32779478). '
                    'all: vm_cast_no_check (eq_refl true).'
                    % (coq_lf(r['pins']), r['L'], r['T'], fmt_nat(r['t']), fmt_nat(r['fuel']), r['M'] + 8))
                   for r in rows[i:i + a.chunk]]
        made.append(write_batch(a.tag, nn, REQ, entries,
                                'quasihalting by the wrapped RepWL tier (rwqh_stage)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
