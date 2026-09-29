#!/usr/bin/env python3
"""Multi-block RepWL finder results -> closeout batches (UNTRUSTED generator).

    python3 tools/closeouttr/mb_batch.py FOUND.json [FOUND2.json ...] --tag MB [--chunk 8]

Takes the `ok` rows of tools/censustr/mb_cert_find.py `find` output that are
still in closeouttr_remaining.txt, and writes theories/CloseoutTr/CBT_<TAG>_<NN>.v
from the next free NN.  Each row is proved by the multi-block RepWL tier
([RepWLMBTr.mb_tier_tr_sound]; a `--qh` row by the wrapped tier through
[RepWLMBTr.mbqh_stage]) re-running the closure and the certificate
search at the finder's parameters (the per-side word lists and thresholds,
an [mbpar] literal) -- no certificate is stored, so a wrong parameter row
fails its [vm_cast] and nothing else.

Compile the batch before committing and time it (SCOPING_INSTR 7.4.MB):
drop a rejected row with --skip SPEC and regenerate.  Then run
tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'censustr'))
from cbt import REPO, next_free, write_batch  # noqa: E402
from mb_cert_find import call_args, call_args_qh  # noqa: E402

REQ = ['From BBB4.CensusTr Require Import RepWLMBTr.']


def proof(r):
    if r.get('qh'):
        # the wrapped tier's bound S t <= B_tr, then the tier itself
        return ('apply coversTr_qh3, (mbqh_stage _ %s 32779478). '
                'all: vm_cast_no_check (eq_refl true).' % call_args_qh(r))
    return ('apply coversTr_nqh, (mb_tier_tr_sound _ %s). '
            'vm_cast_no_check (eq_refl true).' % call_args(r))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='MB')
    ap.add_argument('--chunk', type=int, default=8)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.found:
        for r in json.load(open(f)):
            if r.get('ok') and r['spec'] in remaining \
                    and r['spec'] not in seen and r['spec'] not in a.skip:
                seen.add(r['spec'])
                rows.append(r)
    # heavy rows (by closure size) spread across the batches, so no one
    # batch is the long pole of CI's -j4
    rows.sort(key=lambda r: -r['nodes'])
    nb = (len(rows) + a.chunk - 1) // a.chunk
    groups = [rows[k::nb] for k in range(nb)]
    nn = next_free(a.tag)
    made = []
    for g in groups:
        entries = [(r['spec'], proof(r)) for r in g]
        if a.dry_run:
            print('CBT_%s_%02d: %d rows, %d nodes' % (a.tag, nn, len(g), sum(r['nodes'] for r in g)))
        else:
            made.append(write_batch(a.tag, nn, REQ, entries,
                                    'multi-block RepWL (mb_tier_tr, wrapped: mbqh_stage) at finder parameters'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(groups),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
