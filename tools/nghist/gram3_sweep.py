#!/usr/bin/env python3
"""Full n=3 re-sweep of the unboarded residue (UNTRUSTED).

harvest_sweep.py swept PARAMS=[(2,2,...),(4,2,...)] and QPARAMS likewise --
history depth k varied, GRAM ORDER n never.  Wave-14 measured what that costs:
on the holdout front a pass climbing k to 12 at n=2 boarded ZERO, and a pass
at n=3 boarded FIVE.  The residue's own measured failure mode agrees --
fail_diag.py puts ~85% at NOMEAS, i.e. the closure is fine and the liveness
measure search fails, which is a vocabulary problem that n addresses and k
does not.

So: re-run the 1,244 unboarded residue machines at n=3, BOTH tiers
(never-QH and the R_QH/wrap tier), parallel over cores.

Results are written incrementally so a killed run loses nothing:
    gram3_nqh.tsv   machine k n t fuel nctx   -> holdout_sweep.py emit format
    gram3_qh.tsv    machine q s k n t fuel nctx
Re-running skips machines already present in those files.

Usage:  gram3_sweep.py [WORKERS] [BUDGET_SECONDS]
"""
import os
import signal
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
os.chdir(HERE)
import nghist_prove as P                                    # noqa: E402

NQH_OUT = os.path.join(HERE, 'gram3_nqh.tsv')
QH_OUT = os.path.join(HERE, 'gram3_qh.tsv')
NQH_PARAMS = [(2, 3, 60, 60000), (4, 3, 60, 60000), (6, 3, 80, 120000)]
QH_PARAMS = [(2, 3, 60000), (4, 3, 60000)]
BUDGET = int(sys.argv[2]) if len(sys.argv) > 2 else 120


class Timeout(Exception):
    pass


def _alarm(sig, frm):
    raise Timeout()


def attempt(m):
    """Try never-QH at n=3, then the R_QH/wrap tier.  Returns a result row."""
    signal.signal(signal.SIGALRM, _alarm)
    for (k, n, t, fuel) in NQH_PARAMS:
        signal.alarm(BUDGET)
        try:
            r = P.prove(m, k, n, t, fuel)
        except Exception:
            r = None
        finally:
            signal.alarm(0)
        if r:
            return ('nqh', m, k, n, t, fuel, r['nctx'])
    for (k, n, fuel) in QH_PARAMS:
        signal.alarm(BUDGET)
        try:
            r = P.prove_qh(m, k, n, fuel)
        except Exception:
            r = None
        finally:
            signal.alarm(0)
        if r:
            return ('qh', m, r['q'], r['s'], k, n, r['t'], fuel, r['nctx'])
    return ('miss', m)


def done_set(path):
    if not os.path.exists(path):
        return set()
    return set(l.split('\t')[0] for l in open(path) if l.strip())


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rem = [l.strip() for l in
           open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt')) if l.strip()]
    hold = set(l.strip() for l in
               open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt')) if l.strip())
    already = done_set(NQH_OUT) | done_set(QH_OUT)
    targets = [m for m in rem if m not in hold and m not in already]
    print("gram-3 residue sweep: %d targets (%d already recorded), %d workers, "
          "%ds budget" % (len(targets), len(already), workers, BUDGET), flush=True)

    nqh = open(NQH_OUT, 'a')
    qh = open(QH_OUT, 'a')
    nq = nh = miss = 0
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(attempt, m): m for m in targets}
        for i, fut in enumerate(as_completed(futs), 1):
            row = fut.result()
            if row[0] == 'nqh':
                nq += 1
                nqh.write('\t'.join(str(x) for x in row[1:]) + '\n')
                nqh.flush()
            elif row[0] == 'qh':
                nh += 1
                qh.write('\t'.join(str(x) for x in row[1:]) + '\n')
                qh.flush()
            else:
                miss += 1
            if i % 25 == 0:
                print("  %d/%d  nqh=%d qh=%d miss=%d  (%.1f%% hit)"
                      % (i, len(targets), nq, nh, miss,
                         100.0 * (nq + nh) / i), flush=True)
    nqh.close()
    qh.close()
    tot = nq + nh
    print("gram-3 residue sweep DONE: %d never-QH + %d R_QH = %d hits / %d "
          "(%.1f%%)" % (nq, nh, tot, len(targets),
                        100.0 * tot / max(1, len(targets))), flush=True)


if __name__ == '__main__':
    main()
