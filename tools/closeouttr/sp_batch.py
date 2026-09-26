#!/usr/bin/env python3
"""irules certificates -> closeout batches for class SP (UNTRUSTED generator).

    python3 tools/closeouttr/sp_batch.py probe CERTDIR OUT.tsv [--jobs 4] [--timeout 60]
    python3 tools/closeouttr/sp_batch.py batch OUT.tsv [...] --tag SP [--chunk 50]

The certificates are BBB's `bin/irules --cert-dir` output (the harness
prover: symbolic rules with an affine meta map C(k) ->* C(a*k+b)).  Each
row is proved by the landed transition-level checker
[MetaBlkPfxTr.irulesblkpfx_check_neverqhtr_sound]: the kernel replays the
rules symbolically, so every instruction the meta cycle fires is proved to
recur -- including the rare one that fires once per overflow, which is
exactly what class SP needs.  The certificate literal is stored in the
batch (a few hundred bytes a row; the RepWL route could not do this, its
certificates were megabytes).

`probe` runs the checker on every certificate, one coqc per certificate
under a timeout: an accepted certificate checks in under a second, but a
rejected one can burn its whole fuel (470 s measured), so it must not share
a batch.  `batch` writes theories/CloseoutTr/CBT_<TAG>_<NN>.v from the next
free NN, taking only the rows the probe accepted and that are still in
closeouttr_remaining.txt.  Compile the batch before committing, then run
tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import importlib.util
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "genbp", os.path.join(REPO, "tools", "gen_irulesblkpfx_certs.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

CFUEL = 200000
FUEL = 300000

REQ = ['From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK',
       '     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr.']

PROBE_HEAD = '''From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr.
Import ListNotations.
'''


def cert_term(c):
    """the certificate as one closed Coq term (Z counts, nat step fields)"""
    return ('(mkBIRCertP %d%%nat (%d) (%d) (%d) (%d) %s S%d %s %s %s %s)%%Z'
            % (c["anchor_step"], c["k0"], c["kmin"], c["meta_a"], c["meta_b"],
               G.ST[c["tpl_state"]], c["tpl_hsym"], G.emit_blks(c["blk"]),
               G.emit_tpl(c["tplL"]), G.emit_tpl(c["tplR"]),
               G.emit_rules(c["rules"], c["pfx"])))


def row_literal(spec):
    from cbt import spec_row
    return spec_row(spec)


def proof_text(c):
    return ('apply coversTr_nqh, (irulesblkpfx_check_neverqhtr_sound _ %s %d %d). '
            'vm_cast_no_check (eq_refl true).' % (cert_term(c), CFUEL, FUEL))


def probe_one(path, timeout):
    c = G.parse_cert(path)
    spec = c["machine"]
    src = PROBE_HEAD + (
        'Definition r := %s : list (option Trans).\n'
        'Time Eval vm_compute in irulesblkpfx_check_neverqhtr (row_to_tm r) %s %d %d.\n'
        % (row_literal(spec), cert_term(c), CFUEL, FUEL))
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, 'P.v')
        open(f, 'w').write(src)
        t0 = time.time()
        try:
            out = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', f],
                                 capture_output=True, text=True, timeout=timeout, cwd=d)
            txt = out.stdout + out.stderr
            if '= true' in txt:
                v = 'true'
            elif '= false' in txt:
                v = 'false'
            else:
                v = 'error'
        except subprocess.TimeoutExpired:
            v = 'timeout'
        return spec, path, v, time.time() - t0


def cmd_probe(a):
    certs = sorted(os.path.join(a.certdir, f) for f in os.listdir(a.certdir)
                   if f.endswith('.cert'))
    done = set()
    if os.path.exists(a.out):
        done = set(l.split('\t')[1] for l in open(a.out) if l.strip())
    todo = [p for p in certs if p not in done]
    with open(a.out, 'a') as o, ThreadPoolExecutor(a.jobs) as ex:
        for spec, path, v, dt in ex.map(lambda p: probe_one(p, a.timeout), todo):
            o.write('%s\t%s\t%s\t%.1f\n' % (spec, path, v, dt))
            o.flush()
            print('%-30s %-7s %.1fs' % (spec, v, dt), flush=True)


def cmd_batch(a):
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows, seen = [], set()
    for f in a.probes:
        for line in open(f):
            spec, path, v = line.rstrip('\n').split('\t')[:3]
            if v == 'true' and spec in remaining and spec not in seen \
                    and spec not in a.skip:
                seen.add(spec)
                rows.append((spec, G.parse_cert(path)))
    rows.sort()
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        entries = [(spec, proof_text(c)) for spec, c in rows[i:i + a.chunk]]
        made.append(write_batch(a.tag, nn, REQ, entries,
                                'never-QH by irules certificates (MetaBlkPfxTr)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(rows), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('probe')
    p.add_argument('certdir')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=60)
    b = sub.add_parser('batch')
    b.add_argument('probes', nargs='+')
    b.add_argument('--tag', default='SP')
    b.add_argument('--chunk', type=int, default=50)
    b.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    if a.cmd == 'probe':
        cmd_probe(a)
    else:
        cmd_batch(a)


if __name__ == '__main__':
    main()
