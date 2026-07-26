#!/usr/bin/env python3
"""Laddered n=3 re-sweep of the unboarded residue (UNTRUSTED).

harvest_sweep.py swept PARAMS=[(2,2,...),(4,2,...)] and QPARAMS likewise --
history depth k varied, GRAM ORDER n never.  Wave-14 measured the cost of
that blind spot on the holdout front: climbing k to 12 at n=2 boarded ZERO,
moving to n=3 boarded FIVE.  fail_diag.py already put ~85% of residue
failures at NOMEAS (closure fine, liveness measure search fails), a
vocabulary problem that n addresses and k does not.

LADDERED, one rung per pass -- NOT full escalation per machine.  The first
attempt at this ran a whole 5-rung escalation on each machine and after 16
minutes with 3 busy workers had completed ZERO of 1,244: slow misses at the
expensive rungs block every cheap hit behind them.  Running the cheapest rung
over the WHOLE pool first gets results flowing in minutes and gives an early
read on the hit rate, which is what actually decides whether to spend the
compute on the higher rungs at all.

MISSES ARE RECORDED, per rung.  The first version only tracked hits, so a
preemption would have redone every miss -- and misses are exactly what costs.
In an ephemeral container that is the difference between resuming and
restarting.

    gram3_nqh.tsv        machine k n t fuel nctx     (holdout_sweep.py emit format)
    gram3_qh.tsv         machine q s k n t fuel nctx
    gram3_miss_<k>_<n>   machines that failed that rung

Usage:  gram3_sweep.py K N [WORKERS] [BUDGET] [--qh]
        e.g.  gram3_sweep.py 2 3 3 45        cheapest never-QH rung
              gram3_sweep.py 4 3 3 60        next rung, over rung-1 survivors
              gram3_sweep.py 2 3 3 45 --qh   the R_QH/wrap tier
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

K = int(sys.argv[1])
N = int(sys.argv[2])
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 3
BUDGET = int(sys.argv[4]) if len(sys.argv) > 4 else 45
QH = '--qh' in sys.argv
TAG = "%dq" % K if QH else str(K)
MISS_OUT = os.path.join(HERE, 'gram3_miss_%s_%d.txt' % (TAG, N))
T = 40 + 20 * K
FUEL = 30000 * K


class Timeout(Exception):
    pass


def _alarm(sig, frm):
    raise Timeout()


def attempt(m):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(BUDGET)
    try:
        r = P.prove_qh(m, K, N, FUEL) if QH else P.prove(m, K, N, T, FUEL)
    except Exception:
        r = None
    finally:
        signal.alarm(0)
    if not r:
        return ('miss', m)
    if QH:
        return ('qh', m, r['q'], r['s'], K, N, r['t'], FUEL, r['nctx'])
    return ('nqh', m, K, N, T, FUEL, r['nctx'])


def col0(path):
    if not os.path.exists(path):
        return set()
    return set(l.split('\t')[0].strip() for l in open(path) if l.strip())


def main():
    rem = [l.strip() for l in
           open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt')) if l.strip()]
    hold = set(l.strip() for l in
               open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt')) if l.strip())
    # already decided by ANY rung, plus already tried at THIS rung
    done = col0(NQH_OUT) | col0(QH_OUT) | col0(MISS_OUT)
    targets = [m for m in rem if m not in hold and m not in done]
    print("gram-3 rung k=%d n=%d %s: %d targets (%d already done), %d workers, "
          "%ds budget, fuel=%d" % (K, N, "R_QH" if QH else "never-QH",
                                   len(targets), len(done), WORKERS, BUDGET, FUEL),
          flush=True)
    if not targets:
        return

    hit_f = open(QH_OUT if QH else NQH_OUT, 'a')
    miss_f = open(MISS_OUT, 'a')
    nhit = nmiss = 0
    with ProcessPoolExecutor(max_workers=WORKERS) as ex:
        futs = [ex.submit(attempt, m) for m in targets]
        for i, fut in enumerate(as_completed(futs), 1):
            row = fut.result()
            if row[0] == 'miss':
                nmiss += 1
                miss_f.write(row[1] + '\n')
                miss_f.flush()
            else:
                nhit += 1
                hit_f.write('\t'.join(str(x) for x in row[1:]) + '\n')
                hit_f.flush()
                print("  HIT %s" % row[1], flush=True)
            if i % 25 == 0:
                print("  %d/%d  hits=%d  (%.1f%%)"
                      % (i, len(targets), nhit, 100.0 * nhit / i), flush=True)
    hit_f.close()
    miss_f.close()
    print("rung k=%d n=%d %s DONE: %d hits / %d (%.1f%%)"
          % (K, N, "R_QH" if QH else "never-QH", nhit, len(targets),
             100.0 * nhit / max(1, len(targets))), flush=True)


if __name__ == '__main__':
    main()
