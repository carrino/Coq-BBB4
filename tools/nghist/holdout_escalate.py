#!/usr/bin/env python3
"""Escalation rungs for the holdout survivors (UNTRUSTED).

`holdout_sweep.py` boarded 4 of 20 at the CHEAPEST rung (k=2,n=2).  The
survivors also resisted (4,2) and (6,2) and the whole R_QH/wrap tier, so this
climbs the two axes that rung never touched -- gram order n and history k --
with fuel/seed raised to match.

Caveat worth keeping in mind while reading the results: every hit so far came
at the cheapest rung, which is a mild signal that machines needing more
usually need a DIFFERENT ENGINE rather than bigger parameters.  If this comes
back empty, that is informative -- go to RepWL / irules-QH / LapDecider next,
not to even larger k.

Results append to tools/nghist/holdout_results_esc.tsv in the same format
holdout_sweep.py emit consumes.
"""
import os
import signal
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
os.chdir(HERE)
import nghist_prove as P                                    # noqa: E402

OUT = os.path.join(HERE, 'holdout_results_esc.tsv')
# (k, n, t, fuel) -- the rungs (2,2)/(4,2)/(6,2) are already known to fail.
PARAMS = [(4, 3, 60, 60000), (6, 3, 80, 120000),
          (8, 2, 80, 120000), (8, 3, 120, 240000),
          (12, 2, 150, 400000)]
BUDGET = 300          # seconds per (machine, rung)


class Timeout(Exception):
    pass


def _alarm(sig, frm):
    raise Timeout()


signal.signal(signal.SIGALRM, _alarm)

rem = set(open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt'))
          .read().split())
hold = [l.strip() for l in
        open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt')) if l.strip()]
targets = [h for h in hold if h in rem]

print("escalating NGramHist over %d surviving holdouts, %d rungs, %ds each"
      % (len(targets), len(PARAMS), BUDGET), flush=True)
out = open(OUT, 'w')
hits = 0
for m in targets:
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
            got = (k, n, t, fuel, r['nctx'])
            break
    if got:
        hits += 1
        out.write("%s\t%d\t%d\t%d\t%d\t%d\n" % ((m,) + got))
        out.flush()
        print("  HIT %s k=%d n=%d t=%d fuel=%d nctx=%d" % ((m,) + got),
              flush=True)
    else:
        print("  --  %s" % m, flush=True)
out.close()
print("escalation: %d hits / %d targets -> %s" % (hits, len(targets), OUT),
      flush=True)
