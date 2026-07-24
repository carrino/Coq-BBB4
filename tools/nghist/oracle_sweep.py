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
    """List of (k,n,t,fuel) to try for never-QH, oracle-first then escalation."""
    plans = []
    if m in ORACLE:
        h, g, gas = ORACLE[m]
        k = max(1, h)
        fuel = max(20000, gas * 20)
        for t in (20, 40, 80, 150):
            plans.append((k, g, t, fuel))
        # a slightly richer fallback on the oracle machine
        for t in (40, 150):
            plans.append((max(k, 2), max(g, 2), t, fuel))
    else:
        for (k, n) in ((2, 2), (4, 2), (2, 3), (4, 3)):
            for t in (40, 150):
                plans.append((k, n, t, 20000))
    return plans

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

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'probe':
        probe(int(sys.argv[2]) if len(sys.argv) > 2 else 300)
    elif cmd == 'nqh':
        nqh_pass()
    elif cmd == 'qh':
        qh_pass()
