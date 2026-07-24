#!/usr/bin/env python3
"""Oracle-driven NGramHist sweep of the UNBOARDED census residue (wave-7).

For each unboarded residue machine:
 - if it is oracle-targetable (<=7 transitions, in BB4_verified_enumeration.csv
   as a nonhalt NGRAM row) use mxdys' per-machine params (history->k, gram->n,
   gas->fuel) with a small t escalation;
 - otherwise (all-8, outside mxdys' enumeration) escalate blindly.
Try never-QH (prove) first, then R_QH (prove_qh) on the failures.  The rank
fallback in cert_for_state is exercised on this pass.

Dedup: residue minus the wave-6 manifests (nghstage/nghwstage) minus the
staged-not-wired v5/v5b manifests.  UNTRUSTED: kernel re-checks every cert.

Usage:
  oracle_sweep.py probe [N]   -> stderr yield stats on a sample of N (no write)
  oracle_sweep.py nqh         -> never-QH pass, writes oracle_nqh_results.tsv
  oracle_sweep.py qh          -> R_QH pass over nqh failures, oracle_qh_results.tsv
"""
import sys, os
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nghist_prove as P
import oracle_lookup as O

ROOT = "/home/user/Coq-BBB4"
RES = ROOT + "/tools/census_residue.txt"
MAXCTX = 1200

def col0(path, hdr=False):
    out = set()
    if not os.path.exists(path):
        return out
    for i, l in enumerate(open(path)):
        if hdr and i == 0:
            continue
        l = l.strip()
        if not l or l.startswith('#'):
            continue
        out.add(l.split('\t')[0])
    return out

def boarded():
    s = set()
    s |= col0(ROOT + "/tools/nghstage_manifest.tsv", True)
    s |= col0(ROOT + "/tools/nghwstage_manifest.tsv", True)
    s |= col0(ROOT + "/tools/listc_v5_manifest.tsv", True)
    s |= col0(ROOT + "/tools/listc_v5b_manifest.tsv", True)
    return s

def load_params():
    d = {}
    p = ROOT + "/tools/nghist/oracle_params.csv"
    if os.path.exists(p):
        for i, l in enumerate(open(p)):
            if i == 0 or not l.strip():
                continue
            m, fam, h, g, gas = l.strip().split(',')
            d[m] = (int(h), int(g), int(gas))
    return d

ORACLE = load_params()

def nqh_plan(m):
    """List of (k,n,t,fuel) to try for never-QH, oracle-first then escalation.
    Kept lean (few combos) so the full-residue sweep completes in ~1 container
    window; grow() dominates cost per combo."""
    if m in ORACLE:
        h, g, gas = ORACLE[m]
        k = max(1, h)
        fuel = max(20000, gas * 20)
        return [(k, g, 40, fuel), (max(k, 2), max(g, 2), 40, fuel),
                (max(k, 2), max(g, 2), 150, fuel)]
    return [(2, 2, 40, 20000), (4, 2, 40, 20000), (2, 3, 150, 20000)]

def qh_plan(m):
    plans = []
    if m in ORACLE:
        h, g, gas = ORACLE[m]
        for k in (max(1, h), max(2, h)):
            plans.append((k, g, max(20000, gas * 20)))
    else:
        for (k, n) in ((2, 2), (4, 2), (2, 3)):
            plans.append((k, n, 20000))
    return plans

def try_nqh(m):
    for (k, n, t, fuel) in nqh_plan(m):
        try:
            r = P.prove(m, k, n, t, fuel)
        except Exception:
            r = None
        if r is not None and r['nctx'] <= MAXCTX:
            return (m, 'OK', k, n, t, fuel, r['nctx'])
    return (m, 'FAIL', 0, 0, 0, 0, 0)

def try_qh(m):
    for (k, n, fuel) in qh_plan(m):
        try:
            r = P.prove_qh(m, k, n, fuel)
        except Exception:
            r = None
        if r is not None and r['nctx'] <= MAXCTX:
            return (m, r['q'], r['s'], k, n, r['t'], fuel, r['nctx'])
    return None

def targets():
    res = [l.strip() for l in open(RES) if l.strip()]
    b = boarded()
    return [m for m in res if m not in b]

def probe(n=300):
    tgt = targets()
    sys.stderr.write("unboarded targets=%d (sampling %d)\n" % (len(tgt), n))
    # interleave targetable and full-8 in the sample
    tgtable = [m for m in tgt if m in ORACLE]
    full8 = [m for m in tgt if m not in ORACLE]
    sample = tgtable[:n // 2] + full8[:n - n // 2]
    nqh_ok = qh_ok = 0
    with ProcessPoolExecutor(max_workers=2) as ex:
        res = list(ex.map(try_nqh, sample, chunksize=8))
    fails = []
    for r in res:
        if r[1] == 'OK':
            nqh_ok += 1
        else:
            fails.append(r[0])
    with ProcessPoolExecutor(max_workers=2) as ex:
        qres = list(ex.map(try_qh, fails, chunksize=8))
    qh_ok = sum(1 for q in qres if q)
    sys.stderr.write("SAMPLE %d: never-QH boards %d, R_QH boards %d of %d fails => total %d/%d (%.0f%%)\n" % (
        len(sample), nqh_ok, qh_ok, len(fails), nqh_ok + qh_ok, len(sample),
        100.0 * (nqh_ok + qh_ok) / max(1, len(sample))))
    # split by targetable vs full8
    tset = set(tgtable[:n // 2])
    t_ok = sum(1 for r in res if r[1] == 'OK' and r[0] in tset)
    sys.stderr.write("  targetable sample %d: never-QH %d\n" % (len(tset), t_ok))
    f_ok = nqh_ok - t_ok
    sys.stderr.write("  full-8 sample %d: never-QH %d\n" % (len(sample) - len(tset), f_ok))

def nqh_pass():
    tgt = targets()
    sys.stderr.write("never-QH pass over %d unboarded\n" % len(tgt))
    n = int(os.environ.get('NGH_LIMIT', len(tgt)))
    tgt = tgt[:n]
    ok = 0
    out = ROOT + "/tools/nghist/oracle_nqh_results.tsv"
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=2) as ex:
        for i, r in enumerate(ex.map(try_nqh, tgt, chunksize=8)):
            if r[1] == 'OK':
                ok += 1
                f.write("%s\t%d\t%d\t%d\t%d\t%d\n" % (r[0], r[2], r[3], r[4], r[5], r[6]))
            if (i + 1) % 200 == 0:
                f.flush()
                sys.stderr.write("  %d/%d, %d boardable\n" % (i + 1, len(tgt), ok))
    sys.stderr.write("DONE never-QH %d/%d\n" % (ok, len(tgt)))

def qh_pass():
    tgt = targets()
    done = col0(ROOT + "/tools/nghist/oracle_nqh_results.tsv")
    rem = [m for m in tgt if m not in done]
    sys.stderr.write("R_QH pass over %d (unboarded minus never-QH boards)\n" % len(rem))
    n = int(os.environ.get('NGH_LIMIT', len(rem)))
    rem = rem[:n]
    ok = 0
    out = ROOT + "/tools/nghist/oracle_qh_results.tsv"
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=2) as ex:
        for i, r in enumerate(ex.map(try_qh, rem, chunksize=8)):
            if r:
                ok += 1
                f.write("%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\n" % r)
            if (i + 1) % 200 == 0:
                f.flush()
                sys.stderr.write("  %d/%d, %d boardable\n" % (i + 1, len(rem), ok))
    sys.stderr.write("DONE R_QH %d/%d\n" % (ok, len(rem)))

NQH_OUTDIR = ROOT + "/theories/Machines/NGHStage"
NQH_MANI = ROOT + "/tools/nghstage_manifest.tsv"
QH_OUTDIR = ROOT + "/theories/Machines/NGHWStage"
QH_MANI = ROOT + "/tools/nghwstage_manifest.tsv"

def emit_nqh(start_fi=5, start_idx=500):
    """Emit the never-QH sweep results into NEW continuing files (NGH_05..),
    theorem/def/list names offset by start_idx so nothing clashes with wave-6.
    Appends to the manifest."""
    rows = [l.rstrip('\n').split('\t') for l in
            open(ROOT + "/tools/nghist/oracle_nqh_results.tsv") if l.strip()]
    # skip machines already boarded (safety)
    b = boarded()
    rows = [r for r in rows if r[0] not in b]
    man = open(NQH_MANI, 'a')
    per = 100
    nfiles = (len(rows) + per - 1) // per
    for fi in range(nfiles):
        chunk = rows[fi*per:(fi+1)*per]
        gfi = start_fi + fi
        fname = "NGH_%02d" % gfi
        body = [P.HEADER]
        thms = []
        for j, row in enumerate(chunk):
            m, k, n, t, fuel, nctx = row
            r = P.prove(m, int(k), int(n), int(t), int(fuel))
            idx = start_idx + fi*per + j
            nm = '%05d' % idx
            btext, thm = P.emit(m, r, idx)
            body.append(btext)
            thms.append((thm, 'tm_h_' + nm))
            man.write("%s\t%s\t%s.v\t%s\t%s\t%s\t%s\t%s\n" % (m, thm, fname, k, n, t, fuel, nctx))
        lst = "ngh_%02d" % gfi
        body.append('Definition {} : list TM :=\n  [{}].'.format(
            lst, ';\n   '.join(tm for _, tm in thms)))
        term = "Forall_nil NeverQuasiHaltsSt"
        for thm, _ in reversed(thms):
            term = "Forall_cons _ {} ({})".format(thm, term)
        body.append('Lemma {}_nqh : Forall NeverQuasiHaltsSt {}.'.format(lst, lst))
        body.append('Proof. unfold {}. exact ({}). Qed.'.format(lst, term))
        open(NQH_OUTDIR + "/" + fname + ".v", 'w').write('\n\n'.join(body) + '\n')
        sys.stderr.write("wrote %s (%d machines)\n" % (fname, len(chunk)))
    man.close()

def emit_qh(start_fi=6, start_idx=600):
    rows = [l.rstrip('\n').split('\t') for l in
            open(ROOT + "/tools/nghist/oracle_qh_results.tsv") if l.strip()]
    b = boarded()
    rows = [r for r in rows if r[0] not in b]
    man = open(QH_MANI, 'a')
    per = 100
    nfiles = (len(rows) + per - 1) // per
    for fi in range(nfiles):
        chunk = rows[fi*per:(fi+1)*per]
        gfi = start_fi + fi
        fname = "NGHW_%02d" % gfi
        body = [P.HEADER_QH]
        thms = []
        for j, row in enumerate(chunk):
            m, qst, s, k, n, t, fuel, nctx = row
            r = P.prove_qh(m, int(k), int(n), int(fuel))
            idx = start_idx + fi*per + j
            nm = '%05d' % idx
            btext, thm, tmn = P.emit_qh(m, r, idx)
            body.append(btext)
            thms.append((thm, tmn))
            man.write("%s\t%s\t%s.v\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" % (
                m, thm, fname, qst, s, k, n, t, fuel, nctx))
        lst = "nghw_%02d" % gfi
        body.append('Definition {} : list TM :=\n  [{}].'.format(
            lst, ';\n   '.join(tm for _, tm in thms)))
        term = "Forall_nil iqh"
        for thm, _ in reversed(thms):
            term = "Forall_cons _ {} ({})".format(thm, term)
        body.append('Lemma {}_all : Forall iqh {}.'.format(lst, lst))
        body.append('Proof. unfold {}. exact ({}). Qed.'.format(lst, term))
        open(QH_OUTDIR + "/" + fname + ".v", 'w').write('\n\n'.join(body) + '\n')
        sys.stderr.write("wrote %s (%d machines)\n" % (fname, len(chunk)))
    man.close()

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'probe':
        probe(int(sys.argv[2]) if len(sys.argv) > 2 else 300)
    elif cmd == 'nqh':
        nqh_pass()
    elif cmd == 'qh':
        qh_pass()
    elif cmd == 'emit_nqh':
        emit_nqh()
    elif cmd == 'emit_qh':
        emit_qh()
