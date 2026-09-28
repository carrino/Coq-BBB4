#!/usr/bin/env python3
"""irules certificates of QUASIHALTING rows -> closeout batches (UNTRUSTED).

    python3 tools/closeouttr/dx_irqh_batch.py probe CERTDIR ROWS OUT.tsv [--jobs 4] [--timeout 30]
    python3 tools/closeouttr/dx_irqh_batch.py batch OUT.tsv [...] --tag DXQ [--chunk 50]

The certificates are BBB's `bin/irules --cert-dir` output with
`claim_qh T`: the meta cycle's fired set F leaves out an instruction that
fired before the anchor.  Each row is proved by
[MetaBlkPfxQHTr.irulesblkpfx_check_qhtr_close] (the transition-level twin
of MetaBlkPfxQH): the kernel replays the certificate as MetaBlkPfxTr does,
checks that the witness instruction tz fires at index nz and is not in F,
and concludes NonHalt /\ QHBoundTr 32779478 /\ QuasiHaltsTr (the anchor is
the bound; anchors up to 2^20 are lifted to B_close).

tz is the certificate's first `claim_trans ... F` instruction that fired;
nz its first fire, from a plain simulation.  Only certificates of rows in
ROWS are probed (one coqc per certificate, under a timeout); `batch` takes
the accepted rows still in closeouttr_remaining.txt.
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
from sp_batch import G, cert_term, CFUEL, FUEL  # noqa: E402

REQ = ['From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK',
       '     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxQHTr.']

PROBE_HEAD = '''From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxQHTr.
Import ListNotations.
'''

ST = 'ABCD'


def witness(path):
    """(tz, nz): the first finitely-fired instruction the certificate names,
    and its first fire in a plain simulation"""
    fin = []
    spec = None
    for line in open(path):
        p = line.split()
        if p and p[0] == 'machine':
            spec = p[1]
        if p and p[0] == 'claim_trans' and p[2] == 'F' and int(p[3]) > 0:
            fin.append(p[1])
    if not fin:
        return None
    tz = fin[0]
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for y in range(2):
            e = part[3 * y:3 * y + 3]
            tab[(si, y)] = None if e == '---' else (int(e[0]), 1 if e[1] == 'R' else -1,
                                                    ord(e[2]) - 65)
    tape, q, pos = {}, 0, 0
    for n in range(10 ** 6):
        r = tape.get(pos, 0)
        if '%s%d' % (ST[q], r) == tz:
            return tz, n
        t = tab[(q, r)]
        if t is None:
            return None
        tape[pos] = t[0]
        pos += t[1]
        q = t[2]
    return None


def tz_term(tz):
    return '(St%s, S%s)' % (tz[0], tz[1])


def proof_text(c, tz, nz):
    return ('apply coversTr_qh3, (irulesblkpfx_check_qhtr_close _ %s %s %d %d %d); '
            'vm_cast_no_check (eq_refl true).'
            % (cert_term(c), tz_term(tz), nz, CFUEL, FUEL))


def probe_one(path, timeout):
    c = G.parse_cert(path)
    spec = c["machine"]
    w = witness(path)
    if w is None:
        return spec, path, '-', -1, 'nowit', 0.0
    tz, nz = w
    src = PROBE_HEAD + (
        'Definition r := %s : list (option Trans).\n'
        'Time Eval vm_compute in irulesblkpfx_check_qhtr (row_to_tm r) %s %s %d %d %d.\n'
        'Time Eval vm_compute in (cp_anchor %s <=? 1048576)%%nat.\n'
        % (spec_row(spec), cert_term(c), tz_term(tz), nz, CFUEL, FUEL, cert_term(c)))
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, 'P.v')
        open(f, 'w').write(src)
        t0 = time.time()
        try:
            out = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', f],
                                 capture_output=True, text=True, timeout=timeout, cwd=d)
            txt = out.stdout + out.stderr
            n_true = txt.count('= true')
            v = 'true' if n_true == 2 else 'false' if '= false' in txt else 'error'
        except subprocess.TimeoutExpired:
            v = 'timeout'
        return spec, path, tz, nz, v, time.time() - t0


def cmd_probe(a):
    rows = set(l.split()[0] for l in open(a.rows) if l.strip())
    certs = sorted(os.path.join(a.certdir, f) for f in os.listdir(a.certdir)
                   if f.endswith('.cert') and f[:-5] in rows)
    done = set()
    if os.path.exists(a.out):
        done = set(l.split('\t')[1] for l in open(a.out) if l.strip())
    todo = [p for p in certs if p not in done]
    with open(a.out, 'a') as o, ThreadPoolExecutor(a.jobs) as ex:
        for spec, path, tz, nz, v, dt in ex.map(lambda p: probe_one(p, a.timeout), todo):
            o.write('%s\t%s\t%s\t%d\t%s\t%.1f\n' % (spec, path, tz, nz, v, dt))
            o.flush()
            print('%-30s %s@%d %-7s %.1fs' % (spec, tz, nz, v, dt), flush=True)


def cmd_batch(a):
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.probes:
        for line in open(f):
            spec, path, tz, nz, v = line.rstrip('\n').split('\t')[:5]
            if v == 'true' and spec in remaining and spec not in seen \
                    and spec not in a.skip:
                seen.add(spec)
                rows.append((spec, G.parse_cert(path), tz, int(nz)))
    rows.sort(key=lambda x: x[0])
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        entries = [(spec, proof_text(c, tz, nz)) for spec, c, tz, nz in rows[i:i + a.chunk]]
        made.append(write_batch(a.tag, nn, REQ, entries,
                                'quasihalting by irules certificates (MetaBlkPfxQHTr)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('probe')
    p.add_argument('certdir')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=30)
    b = sub.add_parser('batch')
    b.add_argument('probes', nargs='+')
    b.add_argument('--tag', default='DXQ')
    b.add_argument('--chunk', type=int, default=50)
    b.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    cmd_probe(a) if a.cmd == 'probe' else cmd_batch(a)


if __name__ == '__main__':
    main()
