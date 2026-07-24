#!/usr/bin/env python3
"""Wave-8 sweep: widened measure vocabulary over the unboarded residue.

fail_diag (2026-07-24) showed the unboarded residue is 85% NOMEAS -- closes
fine, fails the liveness measure search.  This sweep re-runs both shapes with
the widened PATTERNS + raised caps in nghist_prove, oracle-first params.

RESUMABLE: results append; already-swept machines are skipped on restart.
Per-machine SIGALRM budget (NGH_TIMEOUT seconds, default 45) so pathological
Bellman searches cannot stall the sweep.  UNTRUSTED: kernel re-checks all.

Usage:
  wave8_sweep.py nqh    -> never-QH pass  (wave8_nqh_results.tsv, append)
  wave8_sweep.py qh     -> R_QH pass over nqh failures (wave8_qh_results.tsv)
  wave8_sweep.py emit_nqh [start_fi start_idx]   (default 8 800)
  wave8_sweep.py emit_qh  [start_fi start_idx]   (default 6 600)
"""
import sys, os, signal
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nghist_prove as P
import oracle_sweep as OS

ROOT = "/home/user/Coq-BBB4"
D = ROOT + "/tools/nghist"
NQH_RES = D + "/wave8_nqh_results.tsv"
NQH_FAIL = D + "/wave8_nqh_fail.txt"
QH_RES = D + "/wave8_qh_results.tsv"
QH_FAIL = D + "/wave8_qh_fail.txt"
MAXCTX = 1200
TIMEOUT = int(os.environ.get('NGH_TIMEOUT', 45))

class Budget(Exception):
    pass

def _alarm(sig, frm):
    raise Budget()

def with_budget(fn, m):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(TIMEOUT)
    try:
        return fn(m)
    except Budget:
        return None
    finally:
        signal.alarm(0)

def _nqh(m):
    for (k, n, t, fuel) in OS.nqh_plan(m):
        try:
            r = P.prove(m, k, n, t, fuel)
        except Budget:
            raise
        except Exception:
            r = None
        if r is not None and r['nctx'] <= MAXCTX:
            return (m, k, n, t, fuel, r['nctx'])
    return None

def _qh(m):
    for (k, n, fuel) in OS.qh_plan(m):
        try:
            r = P.prove_qh(m, k, n, fuel)
        except Budget:
            raise
        except Exception:
            r = None
        if r is not None and r['nctx'] <= MAXCTX:
            return (m, r['q'], r['s'], k, n, r['t'], fuel, r['nctx'])
    return None

def try_nqh(m):
    return m, with_budget(_nqh, m)

def try_qh(m):
    return m, with_budget(_qh, m)

def done_set(*paths):
    s = set()
    for p in paths:
        if not os.path.exists(p):
            continue
        for l in open(p):
            l = l.strip()
            if l:
                s.add(l.split('\t')[0])
    return s

def run_pass(tgt, worker, res_path, fail_path, fmt):
    done = done_set(res_path, fail_path)
    rem = [m for m in tgt if m not in done]
    sys.stderr.write("pass: %d targets, %d already swept, %d to go\n"
                     % (len(tgt), len(tgt) - len(rem), len(rem)))
    n = int(os.environ.get('NGH_LIMIT', len(rem)))
    rem = rem[:n]
    ok = 0
    workers = int(os.environ.get('NGH_WORKERS', 3))
    with open(res_path, 'a') as f, open(fail_path, 'a') as ff, \
         ProcessPoolExecutor(max_workers=workers) as ex:
        for i, (m, r) in enumerate(ex.map(worker, rem, chunksize=2)):
            if r:
                ok += 1
                f.write(fmt % r)
                f.flush()
            else:
                ff.write(m + "\n")
                ff.flush()
            if (i + 1) % 100 == 0:
                sys.stderr.write("  %d/%d, %d boardable\n" % (i + 1, len(rem), ok))
    sys.stderr.write("DONE %d/%d boardable this run\n" % (ok, len(rem)))

def targets():
    """OS.targets(), optionally restricted to a machine-list file
    (NGH_TARGETS) -- e.g. the empirical shape split, so the never-QH pass
    does not burn its timeout rejecting known quasihalters."""
    tgt = OS.targets()
    tf = os.environ.get('NGH_TARGETS')
    if tf:
        keep = set(l.strip() for l in open(tf) if l.strip())
        tgt = [m for m in tgt if m in keep]
    return tgt

def nqh_pass():
    run_pass(targets(), try_nqh, NQH_RES, NQH_FAIL,
             "%s\t%d\t%d\t%d\t%d\t%d\n")

def qh_pass():
    # over nqh failures only (both this wave's and machines never nqh-swept)
    caught = done_set(NQH_RES)
    tgt = [m for m in targets() if m not in caught]
    run_pass(tgt, try_qh, QH_RES, QH_FAIL,
             "%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\n")

def emit_nqh(start_fi=8, start_idx=800):
    rows = [l.rstrip('\n').split('\t') for l in open(NQH_RES) if l.strip()]
    b = OS.boarded()
    rows = [r for r in rows if r[0] not in b]
    man = open(OS.NQH_MANI, 'a')
    per = 100
    for fi in range((len(rows) + per - 1) // per):
        chunk = rows[fi*per:(fi+1)*per]
        gfi = start_fi + fi
        fname = "NGH_%02d" % gfi
        body = [P.HEADER]
        thms = []
        for j, (m, k, n, t, fuel, nctx) in enumerate(chunk):
            r = P.prove(m, int(k), int(n), int(t), int(fuel))
            idx = start_idx + fi*per + j
            btext, thm = P.emit(m, r, idx)
            body.append(btext)
            thms.append((thm, 'tm_h_%05d' % idx))
            man.write("%s\t%s\t%s.v\t%s\t%s\t%s\t%s\t%s\n" % (m, thm, fname, k, n, t, fuel, nctx))
        lst = "ngh_%02d" % gfi
        body.append('Definition {} : list TM :=\n  [{}].'.format(
            lst, ';\n   '.join(tm for _, tm in thms)))
        term = "Forall_nil NeverQuasiHaltsSt"
        for thm, _ in reversed(thms):
            term = "Forall_cons _ {} ({})".format(thm, term)
        body.append('Lemma {}_nqh : Forall NeverQuasiHaltsSt {}.'.format(lst, lst))
        body.append('Proof. unfold {}. exact ({}). Qed.'.format(lst, term))
        open(OS.NQH_OUTDIR + "/" + fname + ".v", 'w').write('\n\n'.join(body) + '\n')
        sys.stderr.write("wrote %s (%d machines)\n" % (fname, len(chunk)))
    man.close()

def emit_qh(start_fi=6, start_idx=600):
    rows = [l.rstrip('\n').split('\t') for l in open(QH_RES) if l.strip()]
    b = OS.boarded()
    rows = [r for r in rows if r[0] not in b]
    man = open(OS.QH_MANI, 'a')
    per = 100
    for fi in range((len(rows) + per - 1) // per):
        chunk = rows[fi*per:(fi+1)*per]
        gfi = start_fi + fi
        fname = "NGHW_%02d" % gfi
        body = [P.HEADER_QH]
        thms = []
        for j, (m, qst, s, k, n, t, fuel, nctx) in enumerate(chunk):
            r = P.prove_qh(m, int(k), int(n), int(fuel))
            idx = start_idx + fi*per + j
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
        open(OS.QH_OUTDIR + "/" + fname + ".v", 'w').write('\n\n'.join(body) + '\n')
        sys.stderr.write("wrote %s (%d machines)\n" % (fname, len(chunk)))
    man.close()

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'nqh':
        nqh_pass()
    elif cmd == 'qh':
        qh_pass()
    elif cmd == 'emit_nqh':
        emit_nqh(*(int(x) for x in sys.argv[2:4])) if len(sys.argv) > 2 else emit_nqh()
    elif cmd == 'emit_qh':
        emit_qh(*(int(x) for x in sys.argv[2:4])) if len(sys.argv) > 2 else emit_qh()
