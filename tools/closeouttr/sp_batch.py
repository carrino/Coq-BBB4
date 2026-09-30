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
exactly what class SP needs.  A v4 certificate ([nvar] > 1: an affine
matrix map x -> M x + c over two or three meta variables) goes to
[MetaBlkPfxMVTr.irulesblkmv_check_neverqhtr_sound] instead.  The certificate literal is stored in the
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
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr
     MetaBlkPfxMVTr.
Import ListNotations.
'''


def parse_cert(path):
    """G.parse_cert plus the v4 matrix meta map (verify.c: [nvar], [mmrow],
    [xmin], [x0], [tplrunmv SIDE IDX SYM MV BE], MV = -1 for a constant
    run).  G.parse_cert skips those lines, so without this a v4
    certificate reads as a v1 one with empty templates and fails."""
    c = G.parse_cert(path)
    mv = {"nvar": 1, "M": {}, "cc": {}, "tplL": {}, "tplR": {}}
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        if p[0] == "nvar":
            mv["nvar"] = int(p[1])
        elif p[0] == "mmrow":
            v = [int(x) for x in p[2:]]
            mv["M"][int(p[1])] = v[:-1]
            mv["cc"][int(p[1])] = v[-1]
        elif p[0] in ("xmin", "x0"):
            mv[p[0]] = [int(x) for x in p[1:]]
        elif p[0] == "tplrunmv":
            side, idx, sym, var, be = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
            mv["tplL" if side == "L" else "tplR"][idx] = (sym, var, be)
    if mv["nvar"] > 1:
        c["mv"] = mv
    return c


def zlist(xs):
    return '[' + '; '.join('(%d)' % x for x in xs) + ']'


def emit_tpl_mv(d):
    return '[' + '; '.join(
        '(%d%%nat, %s, (%d))' % (s, 'None' if v < 0 else 'Some %d%%nat' % v, be)
        for (s, v, be) in (d[i] for i in sorted(d))) + ']'


def cert_term(c):
    """the certificate as one closed Coq term (Z counts, nat step fields)"""
    if "mv" in c:
        mv = c["mv"]
        n = mv["nvar"]
        return ('(mkBIRCertMV %d%%nat %s %s [%s] %s %s S%d %s %s %s %s)%%Z'
                % (c["anchor_step"], zlist(mv["x0"]), zlist(mv["xmin"]),
                   '; '.join(zlist(mv["M"][i]) for i in range(n)),
                   zlist([mv["cc"][i] for i in range(n)]),
                   G.ST[c["tpl_state"]], c["tpl_hsym"], G.emit_blks(c["blk"]),
                   emit_tpl_mv(mv["tplL"]), emit_tpl_mv(mv["tplR"]),
                   G.emit_rules(c["rules"], c["pfx"])))
    return ('(mkBIRCertP %d%%nat (%d) (%d) (%d) (%d) %s S%d %s %s %s %s)%%Z'
            % (c["anchor_step"], c["k0"], c["kmin"], c["meta_a"], c["meta_b"],
               G.ST[c["tpl_state"]], c["tpl_hsym"], G.emit_blks(c["blk"]),
               G.emit_tpl(c["tplL"]), G.emit_tpl(c["tplR"]),
               G.emit_rules(c["rules"], c["pfx"])))


def row_literal(spec):
    from cbt import spec_row
    return spec_row(spec)


def check_name(c):
    return 'irulesblkmv_check_neverqhtr' if "mv" in c else 'irulesblkpfx_check_neverqhtr'


def proof_text(c):
    if "mv" in c:
        return ('apply coversTr_nqh, (irulesblkmv_check_neverqhtr_sound _ %s %d %d). '
                'vm_cast_no_check (eq_refl true).' % (cert_term(c), CFUEL, FUEL))
    return ('apply coversTr_nqh, (irulesblkpfx_check_neverqhtr_sound _ %s %d %d). '
            'vm_cast_no_check (eq_refl true).' % (cert_term(c), CFUEL, FUEL))


def probe_one(path, timeout):
    c = parse_cert(path)
    spec = c["machine"]
    src = PROBE_HEAD + (
        'Definition r := %s : list (option Trans).\n'
        'Time Eval vm_compute in %s (row_to_tm r) %s %d %d.\n'
        % (row_literal(spec), check_name(c), cert_term(c), CFUEL, FUEL))
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
                rows.append((spec, parse_cert(path)))
    rows.sort()
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(rows), a.chunk):
        chunk = rows[i:i + a.chunk]
        entries = [(spec, proof_text(c)) for spec, c in chunk]
        mv = any("mv" in c for _, c in chunk)
        req = [REQ[0], REQ[1].rstrip('.') + ' MetaBlkPfxMVTr.'] if mv else REQ
        made.append(write_batch(a.tag, nn, req, entries,
                                'never-QH by irules certificates (MetaBlkPfxTr%s)'
                                % (' / MetaBlkPfxMVTr' if mv else '')))
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
