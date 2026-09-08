#!/usr/bin/env python3
"""Find and stage transition-level QHBound certificates (UNTRUSTED).

This is the instruction-target twin of tools/gen_provenqh.py.  The scan
records the last firing of every instruction; the finder wraps the complete
claimed-quiet instruction set and mirrors Checkers/WrapTr.v's plain n-gram
closure/liveness gate.  Coq, not this program, is the trust boundary.

  scan LIST OUT.tsv [--steps 2000000]
  find SCAN.tsv OUT.tsv [--limit N] [--jobs N]
  probe CERTS.tsv OUTDIR [--chunk 25]
  stage CERTS.tsv PROBEDIR OUTDIR [--chunk 200] [--start 0]
"""
import argparse
import glob
import multiprocessing as mp
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import bulk_prover as bp  # noqa: E402
sys.path.insert(0, HERE)
from gen_walk_shards import tm_lambda  # noqa: E402

B_TR = 32779478
CAND_N = (2, 3, 4, 5, 6)


def machines(path):
    return [x.strip() for x in open(path) if x.strip() and not x.startswith('#')]


def last_fires(spec, steps):
    tbl = bp.parse(spec); tape = {}; p = q = 0; last = {}
    for i in range(steps):
        x = tape.get(p, 0); tr = tbl[(q, x)]
        if tr is None: break
        last[(q, x)] = i
        w, d, q = tr; tape[p] = w; p += 1 if d == 'R' else -1
    quiet = sorted((q, x, s) for (q, x), s in last.items() if s < steps // 2)
    return quiet


def do_scan(src, out, steps):
    rows = []
    for i, spec in enumerate(machines(src)):
        qs = last_fires(spec, steps)
        rows.append((spec, qs))
        if (i + 1) % 100 == 0: print('%d scanned' % (i + 1), flush=True)
    with open(out, 'w') as f:
        f.write('machine\tsteps\tquiet_instrs\n')
        for spec, qs in rows:
            enc = ','.join('%d:%d:%d' % z for z in qs)
            f.write('%s\t%d\t%s\n' % (spec, steps, enc))
    vals = [(s, m, q, x) for m, qs in rows for q, x, s in qs]
    if vals:
        s, m, q, x = max(vals)
        print('quiet_machines=%d quiet_instructions=%d max_last_fire=%d machine=%s instr=%s%d' %
              (sum(bool(qs) for _, qs in rows), len(vals), s, m, chr(65 + q), x))
        if s >= B_TR:
            sys.exit('BOUND RAISE REQUIRED: S %d > B_tr %d' % (s, B_TR))


def read_scan(path):
    out = []
    for line in open(path).read().splitlines()[1:]:
        f = line.split('\t')
        if len(f) >= 3 and f[2]:
            out.append((f[0], [tuple(map(int, z.split(':'))) for z in f[2].split(',')]))
    return out


def closure(spec, pins, n, t, cap=200000):
    tbl = bp.parse(spec); tape = {}; p = q = 0
    for _ in range(t):
        x = tape.get(p, 0); tr = tbl[(q, x)]
        if tr is None: return None
        w, d, q = tr; tape[p] = w; p += 1 if d == 'R' else -1
    quiet = {(qq, x) for qq, x, _ in pins}
    if (q, tape.get(p, 0)) in quiet: return None
    tw = dict(tbl)
    for tg in quiet: tw[tg] = None
    lo, hi = min([p] + list(tape)), max([p] + list(tape))
    lf = lambda i: tape.get(p - 1 - i, 0)
    rf = lambda i: tape.get(p + 1 + i, 0)
    win = lambda fn, d: tuple(fn(d + i) for i in range(n))
    depth = max(p - lo, hi - p) + n + 2
    lset = {win(lf, d) for d in range(1, depth)}
    rset = {win(rf, d) for d in range(1, depth)}
    a0 = (q, tape.get(p, 0), win(lf, 0), win(rf, 0))
    for _ in range(400):
        seen, todo = set(), [a0]
        while todo:
            a = todo.pop()
            if a in seen: continue
            seen.add(a)
            if len(seen) > cap: return None
            q1, x, lw, rw = a; tr = tw[(q1, x)]
            if tr is None: continue
            w, d, q2 = tr
            if d == 'R':
                for z in (0, 1):
                    rr = rw[1:] + (z,)
                    if rr in rset: todo.append((q2, rw[0], (w,) + lw[:-1], rr))
            else:
                for z in (0, 1):
                    ll = lw[1:] + (z,)
                    if ll in lset: todo.append((q2, lw[0], ll, (w,) + rw[:-1]))
        nl = {a[2] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == 'R'}
        nr = {a[3] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == 'L'}
        if nl <= lset and nr <= rset:
            if any(tw[(a[0], a[1])] is None for a in seen): return None
            return seen, lset, rset, tw
        lset |= nl; rset |= nr
    return None


def live_ok(r):
    seen, lset, rset, tw = r; succ = {}
    for a in seen:
        q, x, lw, rw = a; tr = tw[(q, x)]; out = []
        if tr:
            w, d, q2 = tr
            if d == 'R':
                for z in (0, 1):
                    rr = rw[1:] + (z,); b = (q2, rw[0], (w,) + lw[:-1], rr)
                    if rr in rset and b in seen: out.append(b)
            else:
                for z in (0, 1):
                    ll = lw[1:] + (z,); b = (q2, lw[0], ll, (w,) + rw[:-1])
                    if ll in lset and b in seen: out.append(b)
        succ[a] = out
    for tg in {(a[0], a[1]) for a in seen}:
        nodes = {a for a in seen if (a[0], a[1]) != tg}; color = {}
        def visit(v):
            color[v] = 1
            for w in succ[v]:
                if w not in nodes: continue
                if color.get(w) == 1 or (not color.get(w) and visit(w)): return True
            color[v] = 2; return False
        if any(not color.get(v) and visit(v) for v in nodes): return False
    return True


def find_one(row):
    spec, pins = row
    first = max(s for _, _, s in pins) + 1
    horizons = sorted({first} | {t for t in (64, 256, 1024, 4096, 16384)
                                 if t >= first})
    for n in CAND_N:
        for t in horizons:
            if t >= B_TR: continue
            r = closure(spec, pins, n, t)
            if r is not None and live_ok(r):
                seen, ls, rs, _ = r
                return spec, n, t, 8 * len(seen) + 64, len(ls) + len(rs) + 4, pins
    return None


def do_find(scan, out, limit, jobs):
    rows = read_scan(scan)[:limit or None]
    with mp.Pool(jobs) as pool: got = pool.map(find_one, rows)
    got = [x for x in got if x]
    with open(out, 'w') as f:
        f.write('machine\tn\tt\tfuel\trounds\tpins\n')
        for m, n, t, fuel, rounds, pins in got:
            f.write('%s\t%d\t%d\t%d\t%d\t%s\n' %
                    (m, n, t, fuel, rounds, ','.join('%d:%d:%d' % z for z in pins)))
    print('caught=%d/%d' % (len(got), len(rows)))


HEADER = """From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import NGramTr WrapTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.
"""


def cert_rows(path):
    out = []
    for line in open(path).read().splitlines()[1:]:
        f = line.split('\t')
        if len(f) == 6:
            out.append((f[0],) + tuple(map(int, f[1:5])) +
                       ([tuple(map(int, z.split(':'))) for z in f[5].split(',')],))
    return out


def pins_coq(pins):
    return '[' + '; '.join('((St%s, %s), %d)' %
                            (chr(65 + q), 'S1' if x else 'S0', s)
                            for q, x, s in pins) + ']'


def do_probe(src, outdir, chunk):
    os.makedirs(outdir, exist_ok=True); rows = cert_rows(src)
    for ci in range(0, len(rows), chunk):
        nn = ci // chunk
        with open(os.path.join(outdir, 'ProbeQH_%02d.v' % nn), 'w') as f:
            f.write(HEADER)
            for i, (spec, n, t, fuel, rounds, pins) in enumerate(rows[ci:ci + chunk]):
                nm = 'p%02d_%03d' % (nn, i); f.write('(* %s *)\n%s\n' % (spec, tm_lambda('tm_' + nm, spec)))
                f.write('Eval vm_compute in ngram_check_qhboundtr tm_%s %s %d %d %d %d.\n\n' %
                        (nm, pins_coq(pins), n, t, fuel, rounds))


def verdicts(path):
    out = {}
    for vf in glob.glob(os.path.join(path, 'ProbeQH_*.v')):
        specs = re.findall(r'^\(\* ([0-9A-Z\-]{6}(?:_[0-9A-Z\-]{6}){3}) \*\)', open(vf).read(), re.M)
        of = vf[:-2] + '.out'; vals = []
        if os.path.exists(of): vals = [x == 'true' for x in re.findall(r'^\s*= (true|false)', open(of).read(), re.M)]
        for spec, val in zip(specs, vals): out[spec] = val
    return out


def do_stage(src, probes, outdir, chunk, start):
    vs = verdicts(probes); rows = [r for r in cert_rows(src) if vs.get(r[0])]
    os.makedirs(outdir, exist_ok=True)
    for ci in range(0, len(rows), chunk):
        tag = '%02d' % (start + ci // chunk); cb = rows[ci:ci + chunk]; names = []
        with open(os.path.join(outdir, 'ProvTr_QH_%s.v' % tag), 'w') as f:
            f.write('(** GENERATED by tools/censustr/gen_provtr_qh.py -- DO NOT EDIT. *)\n' + HEADER)
            for spec, n, t, fuel, rounds, pins in cb:
                sid = spec.replace('---', 'XXX'); nm = 'tm_' + sid; names.append(nm)
                f.write('(* %s *)\n%s\n' % (spec, tm_lambda(nm, spec)))
                f.write('Lemma qhtr_%s : NonHalt %s /\\ QHBoundTr %d %s /\\ QuasiHaltsTr %s.\n' % (sid, nm, B_TR, nm, nm))
                f.write('Proof. pose proof (ngram_check_qhboundtr_sound %s %s %d %d %d %d (ltac:(vm_cast_no_check (eq_refl true)))) as H. destruct H as (Hnh&Hbound&Hqh). split; [exact Hnh|split; [intros tg s Hquiet; eapply Nat.le_trans; [exact (Hbound tg s Hquiet)|apply Nat.leb_le; vm_cast_no_check (eq_refl true)]|exact Hqh]]. Qed.\n\n' %
                        (nm, pins_coq(pins), n, t, fuel, rounds))
            f.write('Definition provqh_%s : list TM := [%s].\n' % (tag, '; '.join(names)))
            term = '(Forall_nil _)'
            for nm in reversed(names): term = '(Forall_cons _ qhtr_%s %s)' % (nm[3:], term)
            f.write('Lemma provqh_%s_all : Forall (fun tm => NonHalt tm /\\ QHBoundTr %d tm /\\ QuasiHaltsTr tm) provqh_%s.\nProof. exact %s. Qed.\n' % (tag, B_TR, tag, term))
    print('staged=%d' % len(rows))


def main():
    ap = argparse.ArgumentParser(); sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('scan'); p.add_argument('src'); p.add_argument('out'); p.add_argument('--steps', type=int, default=2000000)
    p = sp.add_parser('find'); p.add_argument('scan'); p.add_argument('out'); p.add_argument('--limit', type=int); p.add_argument('--jobs', type=int, default=3)
    p = sp.add_parser('probe'); p.add_argument('src'); p.add_argument('outdir'); p.add_argument('--chunk', type=int, default=25)
    p = sp.add_parser('stage'); p.add_argument('src'); p.add_argument('probes'); p.add_argument('outdir'); p.add_argument('--chunk', type=int, default=200); p.add_argument('--start', type=int, default=0)
    a = ap.parse_args()
    if a.cmd == 'scan': do_scan(a.src, a.out, a.steps)
    elif a.cmd == 'find': do_find(a.scan, a.out, a.limit, a.jobs)
    elif a.cmd == 'probe': do_probe(a.src, a.outdir, a.chunk)
    else: do_stage(a.src, a.probes, a.outdir, a.chunk, a.start)


if __name__ == '__main__': main()
