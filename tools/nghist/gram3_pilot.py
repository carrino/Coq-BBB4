#!/usr/bin/env python3
"""Does gram order n=3 board residue machines that n=2 could not?  (UNTRUSTED)

WHY: harvest_sweep.py sweeps PARAMS=[(2,2,...),(4,2,...)] and
QPARAMS=[(2,2,...),(4,2,...)] -- it varies HISTORY DEPTH k and never touches
GRAM ORDER n.  Wave-14 hit exactly that blind spot on the holdout front: a
first pass at n=2 boarded 4 of 20, a second pass that climbed k to 12 (still
n=2) boarded 0 more, and a third pass at n=3 boarded 5 -- including both
remaining doubles and three of the four towers, machines whose hand proofs
were estimated at a session each.

k and n are not interchangeable: n is how much of the NEIGHBOURHOOD each
context sees, k is how far BACK it remembers.  The residue's measured
failure mode (tools/nghist/fail_diag.py: ~85% NOMEAS -- closes fine, fails
the liveness measure search) is a vocabulary problem, which is the kind n
helps and k does not.

This is the cheap decisive experiment before committing to a full re-sweep of
1,244 unboarded residue machines: take a random sample, run n=3, and measure
the hit rate on machines the n=2 sweep already gave up on.

Usage:  gram3_pilot.py [SAMPLE] [SEED]
"""
import os
import random
import signal
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
os.chdir(HERE)
import nghist_prove as P                                    # noqa: E402

SAMPLE = int(sys.argv[1]) if len(sys.argv) > 1 else 40
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 20260726
PARAMS = [(2, 3, 60, 60000), (4, 3, 60, 60000), (6, 3, 80, 120000)]
BUDGET = 120


class Timeout(Exception):
    pass


def _alarm(sig, frm):
    raise Timeout()


signal.signal(signal.SIGALRM, _alarm)

rem = [l.strip() for l in
       open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt')) if l.strip()]
hold = set(l.strip() for l in
           open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt')) if l.strip())
residue = [m for m in rem if m not in hold]
random.seed(SEED)
sample = random.sample(residue, min(SAMPLE, len(residue)))

print("gram-3 pilot: %d of %d unboarded residue machines, seed %d"
      % (len(sample), len(residue), SEED), flush=True)
hits = []
for i, m in enumerate(sample):
    got = None
    for (k, n, t, fuel) in PARAMS:
        signal.alarm(BUDGET)
        try:
            r = P.prove(m, k, n, t, fuel)
        except Exception:
            r = None
        finally:
            signal.alarm(0)
        if r:
            got = (k, n, r['nctx'])
            break
    if got:
        hits.append((m,) + got)
        print("  HIT %s k=%d n=%d nctx=%d" % ((m,) + got), flush=True)
print("gram-3 pilot: %d hits / %d sampled  (%.0f%%) -- residue pool is %d"
      % (len(hits), len(sample), 100.0 * len(hits) / len(sample), len(residue)),
      flush=True)
if hits:
    with open(os.path.join(HERE, 'gram3_pilot_hits.tsv'), 'w') as f:
        for m, k, n, nctx in hits:
            f.write("%s\t%d\t%d\t%d\n" % (m, k, n, nctx))
