#!/usr/bin/env python3
"""Instruction-level lap boards -> closeout batches (UNTRUSTED generator).

    python3 tools/counters/emit_lapcert.py --list ROWS --tr --emit --json lap.json
    python3 tools/closeouttr/sp_lap_batch.py lap.json [...] --tag SP [--chunk 50]

`emit_lapcert.py --tr --emit` writes and compiles one board per derived row,
theories/Machines/CountersTr/LAPT_<ID>.v, whose [nqhtr_<ID>] is
[NeverQuasiHaltsTr tm_<ID>] by [LapGlueTr.glue_neverqhtr] (the lap
certificate run on the machine wrapped at its never-fired instructions; the
overflow chain witnesses the counter's rare carry instruction).  This takes
the rows whose board compiled (its .vo is on disk) and that are still in
closeouttr_remaining.txt, lists the boards in _CoqProject, and writes
CBT_<TAG>_<NN>.v rows that apply [coversTr_nqh_at] to the board's theorem.
Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

PREFIX = 'theories/Machines/CountersTr/LAPT_'


def mid(spec):
    return spec.replace('-', '_')


def add_to_coqproject(paths):
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    have = set(lines)
    new = [x for x in paths if x not in have]
    if not new:
        return
    last = max(i for i, l in enumerate(lines) if l.startswith(PREFIX))
    lines[last + 1:last + 1] = new
    open(p, 'w').write('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+', help='emit_lapcert.py --json output')
    ap.add_argument('--tag', default='SP')
    ap.add_argument('--chunk', type=int, default=50)
    ap.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows = set()
    for f in a.found:
        for r in json.load(open(f)):
            s = r.get('spec')
            if not r.get('ok') or not r.get('tr') or s not in remaining or s in a.skip:
                continue
            v = os.path.join(REPO, PREFIX + mid(s) + '.v')
            if os.path.exists(v[:-2] + '.vo') and \
                    'Theorem nqhtr_%s ' % mid(s) in open(v).read():
                rows.add(s)
    rows = sorted(rows)
    add_to_coqproject([PREFIX + mid(s) + '.v' for s in rows])
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        chunk = rows[i:i + a.chunk]
        req = ['From BBB4.Machines.CountersTr Require %s.'
               % ' '.join('LAPT_%s' % mid(s) for s in chunk)]
        entries = [(s, 'apply (coversTr_nqh_at LAPT_%s.tm_%s); '
                       '[exact LAPT_%s.nqhtr_%s | intros q s; destruct q, s; reflexivity].'
                    % (mid(s), mid(s), mid(s), mid(s))) for s in chunk]
        made.append(write_batch(a.tag, nn, req, entries,
                                'never-QH by lap certificates at the instruction '
                                'level (LapGlueTr, LAPT boards)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s'
          % (len(rows), len(made), ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
