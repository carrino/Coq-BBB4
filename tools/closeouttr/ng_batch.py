#!/usr/bin/env python3
"""The n-gram route for the closeout: probe, then batch (UNTRUSTED generator).

    python3 tools/closeouttr/ng_batch.py probe ROWS OUT.json [--rungs R] [--all]
                                               [--jobs N] [--timeout S]
    python3 tools/closeouttr/ng_batch.py batch OUT.json [...] --tag NG [--chunk 25]
    python3 tools/closeouttr/ng_batch.py table OUT.json [--rw RW.json]
    python3 tools/closeouttr/ng_batch.py export OUT.json RESULTS.tsv

The driver IS Coq: every probe is a one-line file

    Eval vm_compute in rank_tier_tr (row_to_tm <row>) n t 200000 512.

compiled by coqc under a timeout, so a probe verdict is the verdict the
batch's [vm_cast_no_check] will get (same checker, same parameters, same
evaluator).  No finder, no certificate literal: the batch re-runs the
check.

A rung is KIND:n:t with KIND
  rk  [DecideTr.rank_tier_tr tm n t 200000 512]    (rank_tier_tr_sound)
  ng  [NGramTr.ngram_check_neverqhtr tm n t 200000 512]
                                                   (ngram_check_neverqhtr_sound)
Default ladder: rk:4:0,rk:5:0,rk:6:0 -- SCOPING_INSTR 7.1y: from window 4
up the instruction target certifies where the census ladder (n <= 3)
could not.  Without --all a row stops at its first accepting rung; with
--all every rung is run (the yield table).  OUT.json is resumable: it
holds {spec: {rung: [verdict, seconds]}} and is rewritten after every
probe; verdict is "true", "false" or "timeout".

`export` writes the probe results as a TSV (spec, rung, verdict, seconds;
one line per probe) so they can be committed; every subcommand that reads
OUT.json also reads such a .tsv.

`batch` takes, per row still in closeouttr_remaining.txt, the cheapest
accepting rung (least time) and writes theories/CloseoutTr/CBT_<TAG>_<NN>.v
from the next free NN.  Compile before committing; drop a rejected row
with --skip SPEC.  Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, spec_row, write_batch  # noqa: E402

FUEL = 200000
ROUNDS = 512
DEFAULT_RUNGS = 'rk:4:0,rk:5:0,rk:6:0'

CHECK = {
    'rk': ('rank_tier_tr', 'rank_tier_tr_sound',
           'From BBB4.CensusTr Require Import DecideTr.'),
    'ng': ('ngram_check_neverqhtr', 'ngram_check_neverqhtr_sound',
           'From BBB4.Checkers Require Import NGramTr.'),
}

PROBE_HDR = ('From Coq Require Import List.\n'
             'From BBB4 Require Import BBB4_Statement BBBT4_Statement.\n'
             'From BBB4.Census Require Import Deferred_Defs.\n'
             '%s\nImport ListNotations.\n')


def parse_rung(s):
    k, n, t = s.split(':')
    assert k in CHECK, s
    return k, int(n), int(t)


def rung_call(rung, tm):
    k, n, t = parse_rung(rung)
    return '%s %s %d %d %d %d' % (CHECK[k][0], tm, n, t, FUEL, ROUNDS)


def coq_probe(job):
    spec, rung, timeout = job
    k = parse_rung(rung)[0]
    src = PROBE_HDR % CHECK[k][2] + \
        'Eval vm_compute in %s.\n' % rung_call(rung, '(row_to_tm %s)' % spec_row(spec))
    fd, path = tempfile.mkstemp(prefix='NGProbe_', suffix='.v')
    with os.fdopen(fd, 'w') as f:
        f.write(src)
    t0 = time.time()
    try:
        p = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', path],
                           capture_output=True, text=True, timeout=timeout)
        out = p.stdout + p.stderr
        v = 'true' if '= true' in out else 'false' if '= false' in out else 'error'
    except subprocess.TimeoutExpired:
        v = 'timeout'
    dt = time.time() - t0
    for ext in ('.v', '.vo', '.vok', '.vos', '.glob'):
        q = path[:-2] + ext
        if os.path.exists(q):
            os.remove(q)
    aux = os.path.join(os.path.dirname(path), '.' + os.path.basename(path)[:-2] + '.aux')
    if os.path.exists(aux):
        os.remove(aux)
    return spec, rung, v, round(dt, 1)


def load(path):
    if not os.path.exists(path):
        return {}
    if path.endswith('.tsv'):
        res = {}
        for l in open(path):
            if l.startswith('#') or not l.strip():
                continue
            s, r, v, dt = l.rstrip('\n').split('\t')
            res.setdefault(s, {})[r] = [v, float(dt)]
        return res
    return json.load(open(path))


def save(path, res):
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(res, f, indent=0, sort_keys=True)
    os.replace(tmp, path)


def probe(a):
    specs = [l.strip() for l in open(a.rows) if l.strip() and not l.startswith('#')]
    rungs = a.rungs.split(',')
    for r in rungs:
        parse_rung(r)
    res = load(a.out)
    pool = mp.Pool(a.jobs)
    # rung by rung, so a row stops at its first accepting rung unless --all
    for r in rungs:
        jobs = []
        for s in specs:
            got = res.get(s, {})
            if r in got:
                continue
            if not a.all and any(v[0] == 'true' for v in got.values()):
                continue
            jobs.append((s, r, a.timeout))
        sys.stderr.write('rung %s: %d probes\n' % (r, len(jobs)))
        for s, rr, v, dt in pool.imap_unordered(coq_probe, jobs):
            res.setdefault(s, {})[rr] = [v, dt]
            save(a.out, res)
            sys.stderr.write('  %s %s %s %.1fs\n' % (s, rr, v, dt))
    pool.close()


def best_rung(got):
    ok = [(dt, r) for r, (v, dt) in got.items() if v == 'true']
    return min(ok)[1] if ok else None


def batch(a):
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows = {}
    for f in a.found:
        for s, got in load(f).items():
            if s in remaining and s not in a.skip and s not in rows:
                r = best_rung(got)
                if r:
                    rows[s] = r
    rows = sorted(rows.items())
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        entries = []
        for s, r in rows[i:i + a.chunk]:
            k, n, t = parse_rung(r)
            entries.append((s, 'apply coversTr_nqh, (%s _ %d %d %d %d). '
                               'vm_cast_no_check (eq_refl true).'
                            % (CHECK[k][1], n, t, FUEL, ROUNDS)))
        kinds = sorted(set(parse_rung(r)[0] for _, r in rows[i:i + a.chunk]))
        made.append(write_batch(a.tag, nn, [CHECK[k][2] for k in kinds], entries,
                                'never-QH by the n-gram rank tier (rank_tier_tr) at window 4-6'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def table(a):
    res = load(a.found[0])
    rwok = None
    if a.rw:
        rwok = set(r['spec'] for r in json.load(open(a.rw)) if r.get('ok'))
    rungs = sorted(set(r for g in res.values() for r in g),
                   key=lambda r: (parse_rung(r)[0], parse_rung(r)[1], parse_rung(r)[2]))
    groups = [('all', lambda s: True)]
    if rwok is not None:
        groups += [('RepWL certifies', lambda s: s in rwok),
                   ('RepWL fails', lambda s: s not in rwok)]
    for name, keep in groups:
        print('%s (%d rows)' % (name, sum(1 for s in res if keep(s))))
        print('| rung | run | true | false | timeout | median s (true) | median s (all run) |')
        print('|---|---:|---:|---:|---:|---:|---:|')
        for r in rungs:
            vs = [res[s][r] for s in res if keep(s) and r in res[s]]
            c = {x: sum(1 for v in vs if v[0] == x) for x in ('true', 'false', 'timeout', 'error')}
            med = lambda xs: '%.1f' % sorted(xs)[len(xs) // 2] if xs else '-'
            print('| %s | %d | %d | %d | %d | %s | %s |' % (
                r, len(vs), c['true'], c['false'], c['timeout'] + c['error'],
                med([v[1] for v in vs if v[0] == 'true']), med([v[1] for v in vs])))
        anyok = sum(1 for s in res if keep(s) and best_rung(res[s]))
        print('any rung: %d\n' % anyok)


def export(a):
    res = load(a.found)
    with open(a.out, 'w') as f:
        f.write('# spec\trung\tverdict\tseconds  (tools/closeouttr/ng_batch.py probe)\n')
        for s in sorted(res):
            for r in sorted(res[s]):
                f.write('%s\t%s\t%s\t%.1f\n' % (s, r, res[s][r][0], res[s][r][1]))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('probe')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--rungs', default=DEFAULT_RUNGS)
    p.add_argument('--all', action='store_true')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=300)
    b = sub.add_parser('batch')
    b.add_argument('found', nargs='+')
    b.add_argument('--tag', default='NG')
    b.add_argument('--chunk', type=int, default=25)
    b.add_argument('--skip', action='append', default=[])
    t = sub.add_parser('table')
    t.add_argument('found', nargs=1)
    t.add_argument('--rw')
    e = sub.add_parser('export')
    e.add_argument('found')
    e.add_argument('out')
    a = ap.parse_args()
    {'probe': probe, 'batch': batch, 'table': table, 'export': export}[a.cmd](a)


if __name__ == '__main__':
    main()
