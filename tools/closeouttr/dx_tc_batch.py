#!/usr/bin/env python3
"""Translated-cycler certificates -> closeout batches (UNTRUSTED generator).

    python3 tools/censustr/tc_find.py ROWS --steps 200000 --maxp 20000 > tc.tsv
    python3 tools/closeouttr/dx_tc_batch.py probe tc.tsv OUT.tsv [--jobs 4] [--timeout 120]
    python3 tools/closeouttr/dx_tc_batch.py batch OUT.tsv [...] --tag DX0 [--chunk 50]

tc_find.py writes (spec, side, n1, P, W) per row it finds periodic; each
row is proved by the landed checker [TCyclerTr.tcycler_check_neverqhtr_sound]
(side R) or [_sound_L] (side L: the checker runs on [mirror_tm]).  `probe`
runs the checker once per certificate under a timeout, one coqc each, so a
verdict is exactly what the batch's [vm_cast_no_check] gets; `batch` writes
theories/CloseoutTr/CBT_<TAG>_<NN>.v from the rows the probe accepted that
are still in closeouttr_remaining.txt.  Then run gen_closeout_tr.py.
"""
import argparse
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, spec_row, write_batch  # noqa: E402

REQ = ['From BBB4 Require Import Mirror.', 'From BBB4.Checkers Require Import TCyclerTr.']

PROBE_HEAD = '''From Coq Require Import List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4 Require Import Mirror.
From BBB4.Checkers Require Import TCyclerTr.
Import ListNotations.
'''


def read_certs(path):
    out = []
    for line in open(path):
        p = line.rstrip('\n').split('\t')
        if len(p) < 5 or p[1] not in ('R', 'L'):
            continue
        out.append((p[0], p[1], int(p[2]), int(p[3]), int(p[4])))
    return out


def target(side):
    return '(row_to_tm r)' if side == 'R' else '(mirror_tm (row_to_tm r))'


def proof_text(side, n1, P, W):
    lem = 'tcycler_check_neverqhtr_sound' if side == 'R' else 'tcycler_check_neverqhtr_sound_L'
    return ('apply coversTr_nqh, (%s _ %d %d %d). vm_cast_no_check (eq_refl true).'
            % (lem, n1, P, W))


def probe_one(c, timeout):
    spec, side, n1, P, W = c
    src = PROBE_HEAD + (
        'Definition r := %s : list (option Trans).\n'
        'Time Eval vm_compute in tcycler_check_neverqhtr %s %d %d %d.\n'
        % (spec_row(spec), target(side), n1, P, W))
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, 'P.v')
        open(f, 'w').write(src)
        t0 = time.time()
        try:
            out = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', f],
                                 capture_output=True, text=True, timeout=timeout, cwd=d)
            txt = out.stdout + out.stderr
            v = 'true' if '= true' in txt else 'false' if '= false' in txt else 'error'
        except subprocess.TimeoutExpired:
            v = 'timeout'
        return c, v, time.time() - t0


def cmd_probe(a):
    done = set()
    if os.path.exists(a.out):
        done = set(l.split('\t')[0] for l in open(a.out) if l.strip())
    todo = [c for c in read_certs(a.certs) if c[0] not in done]
    with open(a.out, 'a') as o, ThreadPoolExecutor(a.jobs) as ex:
        for c, v, dt in ex.map(lambda c: probe_one(c, a.timeout), todo):
            o.write('%s\t%s\t%d\t%d\t%d\t%s\t%.1f\n' % (c + (v, dt)))
            o.flush()
            print('%-30s %-7s %.1fs' % (c[0], v, dt), flush=True)


def cmd_batch(a):
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.probes:
        for line in open(f):
            p = line.rstrip('\n').split('\t')
            spec = p[0]
            if p[5] == 'true' and spec in remaining and spec not in seen \
                    and spec not in a.skip:
                seen.add(spec)
                rows.append((spec, p[1], int(p[2]), int(p[3]), int(p[4])))
    rows.sort()
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        entries = [(c[0], proof_text(*c[1:])) for c in rows[i:i + a.chunk]]
        made.append(write_batch(a.tag, nn, REQ, entries,
                                'never-QH by translated cyclers (TCyclerTr)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('probe')
    p.add_argument('certs')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=120)
    b = sub.add_parser('batch')
    b.add_argument('probes', nargs='+')
    b.add_argument('--tag', default='DX0')
    b.add_argument('--chunk', type=int, default=50)
    b.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    cmd_probe(a) if a.cmd == 'probe' else cmd_batch(a)


if __name__ == '__main__':
    main()
