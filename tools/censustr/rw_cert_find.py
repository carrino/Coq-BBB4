#!/usr/bin/env python3
"""RepWL CERTIFICATE conveyor at the instruction level (UNTRUSTED).

The in-Coq tier [RepWLTr.rw_tier_tr] computes the RepWL closure AND
searches the rank certificate inside vm_compute; on the bouncers the
search is what does not finish (SCOPING_INSTR 7.2a).  Here the search
runs in Python -- the exact mirror of Checkers/RepWL.v that tools/
repwl_prover.py already is, with the avoid filter moved from states to
instructions as CensusTr/RepWLTr.v's [rw_procedure_tr] does -- and Coq
only CHECKS: [rw_check_neverqhtr tm L T t fuel M cert] re-derives the
closure and re-checks every edge of every per-instruction certificate
([rw_check_neverqhtr_sound]).  A wrong certificate fails to typecheck.

  find  ROWS.tsv OUT.json [--jobs N] [--timeout S] [--limit N] [--rows R.tsv]
        [--list MACHINES]
        ROWS: spec L T t fuel M (gen_provtr_rw.py's rows; L candidates
        per spec in file order, then the FALLBACK_L ladder at T=2; t is
        re-tried over 0,64,...,16384).  --list runs every machine of
        the list, the rows' candidates first where it has rows.
        --rows writes the PARAMETER rows of the certified machines
        (spec L T t fuel M, fuel = 8*nodes+64, M = max node size + 8)
        for gen_provtr_rw.py probe/stage: Coq's own [rw_tier_tr] then
        re-runs the search at exactly these parameters (measured within
        10x of this finder) and the stage needs no certificate literal.
  rows  OUT.json R.tsv        the same rows from an existing find output
  probe OUT.json OUTDIR [--chunk 10]     -> ProbeRC_NN.v (+ .names):
        `Eval vm_compute in rw_check_neverqhtr ...` per certificate
  stage OUT.json PROBEDIR OUTDIR --start N [--chunk 50]
        -> ProvTr_RC_NN.v: prc_NN : list TM; prc_NN_nqhtr : Forall
        NeverQuasiHaltsTr prc_NN, for the certificates whose probe
        printed true.  Refuses to overwrite an existing stage.
"""
import argparse
import glob
import json
import multiprocessing as mp
import os
import re
import signal
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools'))
sys.path.insert(0, HERE)
import repwl_prover as rp  # noqa: E402
from gen_walk_shards import tm_lambda  # noqa: E402

T_CANDS = (0, 64, 256, 1024, 4096, 16384)
# closures past this are not handed to Coq's tier: its search on a 52K-node
# closure was OOM-killed at 15 GB after 980 s (a 25K one took 709 s)
MAX_NODES = 30000
# block lengths tried after the rows' own (the tape-period detector's p, 2p):
# measured 2026-09-18, a bouncer whose detector said p=2 closes only at L=3, 6
FALLBACK_L = (2, 3, 4, 5, 6, 7, 8, 9, 10, 12)
MEAS_CTOR = {'N/A': 'RwNA', 'N/L': 'RwNL', 'N/R': 'RwNR', '0/l': 'RwZL', '0/r': 'RwZR'}
INSTRS = [(q, s) for q in range(4) for s in range(2)]


def instr(a):
    """rconf -> Instr, mirror of RepWLTr.rw_instr: (state, head symbol)."""
    return (a[0], a[3])


def asz(a):
    """mirror of RepWLSearch.rw_asz"""
    return len(a[1]) + len(a[5]) + len(a[2]) + len(a[4])


def fired_prefix(tbl, t):
    """instructions fired in the first t steps (mirror of cfires)"""
    q, l, h, r = 0, [], 0, []
    out = set()
    for _ in range(t):
        tr = tbl[(q, h)]
        if tr is None:
            break
        out.add((q, h))
        w, d, q2 = tr
        if d == 'R':
            l, h, r = [w] + l, (r[0] if r else 0), r[1:]
        else:
            l, h, r = l[1:], (l[0] if l else 0), [w] + r
        q = q2
    return out


def procedure_tr(tbl, seen, adj, tg, cands):
    """rp.procedure with the avoid filter on the INSTRUCTION (mirror of
    RepWLTr.rw_procedure_tr / irows_tr): comps or None."""
    nodes = [a for a in seen if instr(a) != tg]
    Kc = len(nodes) + 2
    alive = {}
    for a in nodes:
        for b in adj[a]:
            if instr(b) != tg:
                alive[(a, b)] = True
    comps = []
    for _ in range(300):
        am = {}
        for (u, v) in alive:
            am.setdefault(u, []).append(v)
        comp_list = rp.sccs(nodes, lambda v: am.get(v, []))
        cyclic = [c for c in comp_list if len(c) > 1 or c[0] in am.get(c[0], [])]
        if not cyclic:
            rank = {v: 0 for v in nodes}
            for _ in range(len(nodes) + 1):
                ch = False
                for (u, v) in alive:
                    if rank[u] < rank[v] + 1:
                        rank[u] = rank[v] + 1
                        ch = True
                if not ch:
                    break
            comps.append(("rank", rank))
            return comps
        cidx = {}
        for i, c in enumerate(comp_list):
            for v in c:
                cidx[v] = i
        crank = {i: 0 for i in range(len(comp_list))}
        for _ in range(len(comp_list) + 1):
            ch = False
            for (u, v) in alive:
                if cidx[u] != cidx[v] and crank[cidx[u]] < crank[cidx[v]] + 1:
                    crank[cidx[u]] = crank[cidx[v]] + 1
                    ch = True
            if not ch:
                break
        comps.append(("rank", {v: crank[cidx[v]] for v in nodes}))
        progress = False
        for c in cyclic:
            cs = set(c)
            intra = [(u, v) for (u, v) in alive if u in cs and v in cs]
            done = False
            for m in cands:
                ds = {e: rp.rw_delta(tbl, m, e[0]) for e in intra}
                if all(x <= 0 for x in ds.values()) and any(x < 0 for x in ds.values()):
                    comps.append(("meas", m, 1, {v: 0 for v in c}, cs))
                    for e in intra:
                        if ds[e] < 0:
                            del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            for m in cands:
                W = [(u, v, Kc * rp.rw_delta(tbl, m, u) + 1) for (u, v) in intra]
                phi = rp.bellman(list(cs), W)
                if phi is not None:
                    comps.append(("meas", m, Kc, phi, cs))
                    for e in intra:
                        del alive[e]
                    progress = True
                    break
        if not progress:
            return None
    return None


def lex_check_tr(tbl, adj, seen, tg, comps):
    """mirror of ClosureTr.lex_ok_tr over the tg-avoiding graph"""
    for fa in seen:
        if instr(fa) == tg:
            continue
        for fb in adj[fa]:
            if instr(fb) == tg:
                continue
            if not rp.lex_edge_ok(tbl, comps, fa, fb):
                return False
    return True


def read_scan(path):
    """trcensus output -> {spec: (budget_hint, {instr: (cnt, last)})}"""
    out = {}
    for line in open(path):
        f = line.split()
        if len(f) < 9 or not f[1].startswith('T'):
            continue
        d = {}
        for tok in f[1:9]:
            m = re.match(r'^T([A-D])([01]):(\d+):(\d+)$', tok)
            if m:
                d[(ord(m.group(1)) - 65, int(m.group(2)))] = (int(m.group(3)), int(m.group(4)))
        out[f[0]] = d
    return out


def build_closure_from(tblw, L, T, a0, cap=rp.CAP_NODES):
    """rp.build_closure with the seed given (the seed is taken on the
    ORIGINAL machine at t; the successors on the WRAPPED one)"""
    seen = set()
    todo = [a0]
    while todo:
        a = todo.pop()
        if a in seen:
            continue
        seen.add(a)
        if len(seen) > cap:
            return None
        sl = rp.rw_succs(tblw, L, T, a)
        if sl is None:
            return None
        todo.extend(sl)
    return seen


def find_one_qh(job):
    spec, rows, timeout, scan = job
    tbl = rp.parse(spec)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    t0 = time.time()
    lasts = [l for c, l in scan.values() if c > 0]
    horizon = max(lasts) + 1 if lasts else 0
    pins = {tg: l for tg, (c, l) in scan.items() if c > 0 and l < horizon // 10}
    if not pins:
        return dict(spec=spec, ok=False, why='no quiet instruction in the scan', secs=0.0)
    tblw = dict(tbl)
    for tg in pins:
        tblw[tg] = None
    tmin = max(pins.values()) + 1
    why = 'no closure'
    rows = list(rows) + [(L, 2) for L in FALLBACK_L if (L, 2) not in rows]
    try:
        for (L, T) in rows:
            for t in [x for x in T_CANDS if x >= tmin] or [tmin]:
                a0 = rp.seed(tbl, L, T, t)
                if a0 is None:
                    continue
                seen = build_closure_from(tblw, L, T, a0)
                if seen is None:
                    continue
                adj = {a: rp.rw_succs(tblw, L, T, a) for a in seen}
                targets = sorted({instr(a) for a in seen})
                ok = True
                for tg in targets:
                    comps = procedure_tr(tblw, seen, adj, tg, rp.MEAS)
                    if comps is None or not lex_check_tr(tblw, adj, seen, tg, comps):
                        ok = False
                        why = 'no cert for %s%d at L=%d t=%d (%d nodes)' % (chr(65 + tg[0]), tg[1], L, t, len(seen))
                        break
                if not ok:
                    continue
                signal.alarm(0)
                return dict(spec=spec, ok=True, qh=True, L=L, T=T, t=t, fuel=8 * len(seen) + 64,
                            M=max(asz(a) for a in seen), nodes=len(seen), secs=round(time.time() - t0, 1),
                            pins=sorted((q, sy, l) for (q, sy), l in pins.items()))
    except Timeout:
        why = 'timeout'
    except RecursionError:
        why = 'recursion'
    signal.alarm(0)
    return dict(spec=spec, ok=False, why=why, secs=round(time.time() - t0, 1))


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout()


def find_one(job):
    spec, rows, timeout = job
    tbl = rp.parse(spec)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    t0 = time.time()
    why = 'no closure'
    rows = list(rows) + [(L, 2) for L in FALLBACK_L if (L, 2) not in rows]
    try:
        for (L, T) in rows:
            for t in T_CANDS:
                r = rp.build_closure(tbl, L, T, t)
                if r is None:
                    continue
                a0, seen = r
                adj = {a: rp.rw_succs(tbl, L, T, a) for a in seen}
                targets = sorted({instr(a) for a in seen} | fired_prefix(tbl, t))
                certs = {}
                ok = True
                for tg in targets:
                    comps = procedure_tr(tbl, seen, adj, tg, rp.MEAS)
                    if comps is None or not lex_check_tr(tbl, adj, seen, tg, comps):
                        ok = False
                        why = 'no cert for %s%d at L=%d t=%d (%d nodes)' % (chr(65 + tg[0]), tg[1], L, t, len(seen))
                        break
                    certs[tg] = comps
                if not ok:
                    continue
                signal.alarm(0)
                M = max(asz(a) for a in seen)
                return dict(spec=spec, ok=True, L=L, T=T, t=t, fuel=8 * len(seen) + 64, M=M,
                            nodes=len(seen), secs=round(time.time() - t0, 1),
                            certs={'%d,%d' % tg: [enc_comp(c) for c in comps] for tg, comps in certs.items()})
    except Timeout:
        why = 'timeout'
    except RecursionError:
        why = 'recursion'
    signal.alarm(0)
    return dict(spec=spec, ok=False, why=why, secs=round(time.time() - t0, 1))


def enc_comp(comp):
    """comps with rconf keys -> JSON-able with rconf_enc keys"""
    if comp[0] == 'rank':
        return ['rank', sorted((rp.rconf_enc(a), v) for a, v in comp[1].items() if v != 0)]
    _, m, K, phi, gate = comp
    return ['meas', m, K, sorted((rp.rconf_enc(a), v) for a, v in phi.items() if v != 0),
            sorted(rp.rconf_enc(a) for a in gate)]


def read_rows(path):
    rows = {}
    order = []
    for line in open(path):
        f = line.strip().split('\t')
        if len(f) < 3 or not re.match(r'^[0-9A-Z\-]{6}(_[0-9A-Z\-]{6}){3}$', f[0]):
            continue
        if f[0] not in rows:
            order.append(f[0])
        rows.setdefault(f[0], []).append((int(f[1]), int(f[2])))
    return [(sp, rows[sp]) for sp in order]


def do_find(a):
    specs = read_rows(a.rows)
    if a.list:
        have = dict(specs)
        specs = [(sp, have.get(sp, [])) for sp in (l.strip() for l in open(a.list)) if sp]
    if a.limit:
        specs = specs[:a.limit]
    if a.qh:
        scan = read_scan(a.scan)
        jobs = [(sp, rws, a.timeout, scan.get(sp, {})) for sp, rws in specs]
        fn = find_one_qh
    else:
        jobs = [(sp, rws, a.timeout) for sp, rws in specs]
        fn = find_one
    out = []
    with mp.Pool(a.jobs, maxtasksperchild=20) as pool:
        for i, r in enumerate(pool.imap_unordered(fn, jobs)):
            if r['ok'] and r['nodes'] > MAX_NODES:
                r = dict(spec=r['spec'], ok=False, why='closure of %d nodes past MAX_NODES=%d (found at L=%d t=%d)' % (r['nodes'], MAX_NODES, r['L'], r['t']), secs=r['secs'])
            out.append(r)
            print('%4d/%d %-40s %s' % (i + 1, len(jobs), r['spec'],
                                       ('OK L=%d t=%d nodes=%d %.0fs' % (r['L'], r['t'], r['nodes'], r['secs']))
                                       if r['ok'] else 'no: %s (%.0fs)' % (r['why'], r['secs'])), flush=True)
    json.dump(out, open(a.out, 'w'))
    nok = sum(r['ok'] for r in out)
    print('%d / %d certificates -> %s' % (nok, len(out), a.out))
    if a.rows:
        write_rows(out, a.rows)


def write_rows(out, path):
    n = 0
    with open(path, 'w') as f:
        for r in out:
            if r['ok']:
                f.write('%s\t%d\t%d\t%d\t%d\t%d\n' % (r['spec'], r['L'], r['T'], r['t'], r['fuel'], r['M'] + 8))
                n += 1
    print('%d parameter row(s) -> %s' % (n, path))


# ---- Coq rendering ----

def fmt_nat(v):
    if v <= 5000:
        return str(v)
    return '(%s * 1000 + %d)' % (fmt_nat(v // 1000), v % 1000)


def coq_phi(items):
    if not items:
        return '[]'
    return '[' + '; '.join('(%d%%positive, %s)' % (e, fmt_nat(v)) for e, v in items) + ']'


def coq_gate(items):
    if not items:
        return '[]'
    return '[' + '; '.join('%d%%positive' % e for e in items) + ']'


def coq_comp(c):
    if c[0] == 'rank':
        return 'RwRankE %s' % coq_phi(c[1])
    _, m, K, phi, gate = c
    return 'RwMeasE %s %s %s %s' % (MEAS_CTOR[m], fmt_nat(K), coq_phi(phi), coq_gate(gate))


def coq_cert(name, certs):
    arms = []
    for k, comps in sorted(certs.items()):
        q, s = map(int, k.split(','))
        arms.append('  | (St%s, S%d) => [%s]' % (chr(65 + q), s, ';\n      '.join(coq_comp(c) for c in comps)))
    if len(certs) < 8:
        arms.append('  | _ => []')
    return 'Definition %s (tg : Instr) : list rwcomp :=\n  match tg with\n%s\n  end.' % (name, '\n'.join(arms))


def call_args(r):
    return '%d %d %s %s %d' % (r['L'], r['T'], fmt_nat(r['t']), fmt_nat(r['fuel']), r['M'])


HEADER = '''From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Checkers Require Import RepWL.
From BBB4.CensusTr Require Import RepWLTr.
Import ListNotations.
'''


def certs_of(path):
    return [r for r in json.load(open(path)) if r['ok']]


def do_probe(a):
    rs = certs_of(a.src)
    os.makedirs(a.outdir, exist_ok=True)
    for ci in range(0, len(rs), a.chunk):
        nn = ci // a.chunk
        with open(os.path.join(a.outdir, 'ProbeRC_%02d.v' % nn), 'w') as f, \
                open(os.path.join(a.outdir, 'ProbeRC_%02d.names' % nn), 'w') as g:
            f.write(HEADER)
            for i, r in enumerate(rs[ci:ci + a.chunk]):
                nm = 'p%02d_%03d' % (nn, i)
                f.write('(* %s  L=%d T=%d t=%d fuel=%d M=%d nodes=%d *)\n' % (r['spec'], r['L'], r['T'], r['t'], r['fuel'], r['M'], r['nodes']))
                f.write(tm_lambda('tm_' + nm, r['spec']) + '\n')
                f.write(coq_cert('cert_' + nm, r['certs']) + '\n')
                f.write('Eval vm_compute in rw_check_neverqhtr tm_%s %s cert_%s.\n\n' % (nm, call_args(r), nm))
                g.write(r['spec'] + '\n')
    print('%d certificates -> %d probe file(s) in %s' % (len(rs), (len(rs) + a.chunk - 1) // a.chunk, a.outdir))


def read_verdicts(probedir, prefix='ProbeRC_'):
    vs = {}
    missing = 0
    for nf in sorted(glob.glob(os.path.join(probedir, prefix + '*.names')),
                     key=lambda p: int(re.search(r'_(\d+)\.names$', p).group(1))):
        specs = [l.strip() for l in open(nf) if l.strip()]
        of = nf[:-len('.names')] + '.out'
        got = []
        if os.path.exists(of):
            got = [m == 'true' for m in re.findall(r'^\s*= (true|false)', open(of).read(), re.M)]
        for i, sp in enumerate(specs):
            if i < len(got):
                vs[sp] = got[i]
            else:
                missing += 1
        if len(got) < len(specs):
            sys.stderr.write('%s: %d of %d rungs have no verdict\n' % (os.path.basename(of), len(specs) - len(got), len(specs)))
    if missing:
        sys.stderr.write('%d certificate(s) unprobed in all\n' % missing)
    return vs


STAGE_HEADER = '''(** GENERATED by tools/censustr/rw_cert_find.py -- DO NOT EDIT.

    Transition-level proven-tier stage RC {NN}: {CNT} machines closed by
    the instruction-level RepWL CHECKER ([RepWLTr.rw_check_neverqhtr])
    on a certificate found offline (closure + per-instruction rank
    components; the kernel re-derives the closure and re-checks every
    edge).  Append [prc_{NN}] to [prov_tr] (CensusTr/RunTr.v). *)
''' + HEADER


def do_stage(a):
    vs = read_verdicts(a.probes)
    rs = [r for r in certs_of(a.src) if vs.get(r['spec'])]
    os.makedirs(a.outdir, exist_ok=True)
    n = a.start
    for ci in range(0, len(rs), a.chunk):
        nn = '%02d' % n
        path = os.path.join(a.outdir, 'ProvTr_RC_%s.v' % nn)
        if os.path.exists(path):
            sys.exit('refusing to overwrite %s: pass --start past the existing stages' % path)
        cb = rs[ci:ci + a.chunk]
        names = []
        with open(path, 'w') as f:
            f.write(STAGE_HEADER.replace('{NN}', nn).replace('{CNT}', str(len(cb))) + '\n')
            for k, r in enumerate(cb):
                nm = 'rc%s_%04d' % (nn, k)
                names.append(nm)
                f.write('(* %s  L=%d T=%d t=%d fuel=%d M=%d nodes=%d *)\n' % (r['spec'], r['L'], r['T'], r['t'], r['fuel'], r['M'], r['nodes']))
                f.write(tm_lambda('tm_' + nm, r['spec']) + '\n')
                f.write(coq_cert('cert_' + nm, r['certs']) + '\n')
                f.write('Lemma nqhtr_%s : NeverQuasiHaltsTr tm_%s.\n'
                        'Proof. apply (rw_check_neverqhtr_sound _ %s cert_%s). '
                        'vm_cast_no_check (eq_refl true). Qed.\n\n' % (nm, nm, call_args(r), nm))
            f.write('Definition prc_%s : list TM :=\n  [' % nn)
            f.write(';\n   '.join('tm_%s' % x for x in names))
            f.write('].\n\nLemma prc_%s_nqhtr : Forall NeverQuasiHaltsTr prc_%s.\n' % (nn, nn))
            term = '(Forall_nil NeverQuasiHaltsTr)'
            for x in reversed(names):
                term = '(Forall_cons _ nqhtr_%s %s)' % (x, term)
            f.write('Proof. exact %s. Qed.\n' % term)
        n += 1
    print('%d certified -> %d stage file(s) (ProvTr_RC_%02d..)' % (len(rs), n - a.start, a.start))


def coq_lf(pins):
    return '[' + '; '.join('((St%s, S%d), %s)' % (chr(65 + q), sy, fmt_nat(l)) for q, sy, l in pins) + ']'


QH_HEADER = '''From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.CensusTr Require Import TNF_QHTr RepWLTr QHConveyorTr.
Import ListNotations.
'''


def do_probe_qh(a):
    rs = certs_of(a.src)
    os.makedirs(a.outdir, exist_ok=True)
    for ci in range(0, len(rs), a.chunk):
        nn = ci // a.chunk
        with open(os.path.join(a.outdir, 'ProbeRQ_%02d.v' % nn), 'w') as f, \
                open(os.path.join(a.outdir, 'ProbeRQ_%02d.names' % nn), 'w') as g:
            f.write(QH_HEADER)
            for i, r in enumerate(rs[ci:ci + a.chunk]):
                nm = 'q%02d_%03d' % (nn, i)
                f.write('(* %s  L=%d T=%d t=%d fuel=%d M=%d nodes=%d *)\n' % (r['spec'], r['L'], r['T'], r['t'], r['fuel'], r['M'] + 8, r['nodes']))
                f.write(tm_lambda('tm_' + nm, r['spec']) + '\n')
                f.write('Eval vm_compute in rw_tier_qhbtr tm_%s %s %d %d %s %s %d.\n\n'
                        % (nm, coq_lf(r['pins']), r['L'], r['T'], fmt_nat(r['t']), fmt_nat(r['fuel']), r['M'] + 8))
                g.write(r['spec'] + '\n')
    print('%d rows -> %d probe file(s) in %s' % (len(rs), (len(rs) + a.chunk - 1) // a.chunk, a.outdir))


QH_STAGE_HEADER = '''(** GENERATED by tools/censustr/rw_cert_find.py stage-qh -- DO NOT EDIT.

    Transition-level proven-QH stage {NN}: {CNT} quiet-instruction
    bouncers closed by the wrapped RepWL tier ([RepWLTr.rw_tier_qhbtr]:
    the quiet instructions pinned at their last fires, the closure and
    the rank search on the wrapped machine) via [QHConveyorTr.rwqh_stage].
    Append [pqh_{NN}] to [provqh_tr] (CensusTr/RunTr.v). *)
''' + QH_HEADER
PRED = '(fun tm => NonHalt tm /\\ QHBoundTr 32779478 tm /\\ QuasiHaltsTr tm)'


def do_stage_qh(a):
    vs = read_verdicts(a.probes, 'ProbeRQ_')
    rs = [r for r in certs_of(a.src) if vs.get(r['spec'])]
    os.makedirs(a.outdir, exist_ok=True)
    n = a.start
    for ci in range(0, len(rs), a.chunk):
        nn = '%02d' % n
        path = os.path.join(a.outdir, 'ProvTr_QH_%s.v' % nn)
        if os.path.exists(path):
            sys.exit('refusing to overwrite %s: pass --start past the existing stages' % path)
        cb = rs[ci:ci + a.chunk]
        names = []
        with open(path, 'w') as f:
            f.write(QH_STAGE_HEADER.replace('{NN}', nn).replace('{CNT}', str(len(cb))) + '\n')
            for k, r in enumerate(cb):
                nm = 'rq%s_%04d' % (nn, k)
                names.append(nm)
                f.write('(* %s  L=%d T=%d t=%d fuel=%d M=%d nodes=%d *)\n' % (r['spec'], r['L'], r['T'], r['t'], r['fuel'], r['M'] + 8, r['nodes']))
                f.write(tm_lambda('tm_' + nm, r['spec']) + '\n')
                f.write('Lemma qhtr_%s : NonHalt tm_%s /\\ QHBoundTr 32779478 tm_%s /\\ QuasiHaltsTr tm_%s.\n'
                        'Proof. apply (rwqh_stage tm_%s %s %d %d %s %s %d 32779478). '
                        'all: vm_cast_no_check (eq_refl true). Qed.\n\n'
                        % (nm, nm, nm, nm, nm, coq_lf(r['pins']), r['L'], r['T'], fmt_nat(r['t']), fmt_nat(r['fuel']), r['M'] + 8))
            f.write('Definition pqh_%s : list TM :=\n  [' % nn)
            f.write(';\n   '.join('tm_%s' % x for x in names))
            f.write('].\n\nLemma pqh_%s_qhtr : Forall %s pqh_%s.\n' % (nn, PRED, nn))
            term = '(Forall_nil _)'
            for x in reversed(names):
                term = '(Forall_cons _ qhtr_%s %s)' % (x, term)
            f.write('Proof. exact %s. Qed.\n' % term)
        n += 1
    print('%d certified -> %d stage file(s) (ProvTr_QH_%02d..)' % (len(rs), n - a.start, a.start))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find'); p.add_argument('rows'); p.add_argument('out')
    p.add_argument('--jobs', type=int, default=3); p.add_argument('--timeout', type=int, default=300)
    p.add_argument('--limit', type=int, default=0); p.add_argument('--rows')
    p.add_argument('--qh', action='store_true'); p.add_argument('--scan')
    p.add_argument('--list', help='machine list: rows from ROWS where present, the fallback ladder otherwise')
    p = sp.add_parser('rows'); p.add_argument('src'); p.add_argument('out')
    p = sp.add_parser('probe-qh'); p.add_argument('src'); p.add_argument('outdir'); p.add_argument('--chunk', type=int, default=10)
    p = sp.add_parser('stage-qh'); p.add_argument('src'); p.add_argument('probes'); p.add_argument('outdir')
    p.add_argument('--start', type=int, required=True); p.add_argument('--chunk', type=int, default=100)
    p = sp.add_parser('probe'); p.add_argument('src'); p.add_argument('outdir'); p.add_argument('--chunk', type=int, default=10)
    p = sp.add_parser('stage'); p.add_argument('src'); p.add_argument('probes'); p.add_argument('outdir')
    p.add_argument('--start', type=int, required=True); p.add_argument('--chunk', type=int, default=50)
    a = ap.parse_args()
    if a.cmd == 'rows':
        write_rows(json.load(open(a.src)), a.out)
        return
    {'find': do_find, 'probe': do_probe, 'stage': do_stage,
     'probe-qh': do_probe_qh, 'stage-qh': do_stage_qh}[a.cmd](a)


if __name__ == '__main__':
    main()
