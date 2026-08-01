#!/usr/bin/env python3
"""UNTRUSTED: pin the (k, n, t, fuel) at which the NGramHist closure
discharges every state BUT [qext] on a given row.

The [ReachSt] emitter (tools/nghist/reachst_prove.py) hard-codes qext to the
sparse state of a ReachSt flavour.  On rows 1 and 4 of docs/WAVE36_MXDYS_FOUR
the sparse state is [StD] and no ReachSt flavour matches, so the liveness of
[StD] is supplied by a hand proof instead.  This script only answers the
other half: at which parameters does the closure cover A, B, C?

  python3 tools/mxdys4/pin_kn.py <spec> [qext]

Nothing here carries proof weight; the kernel re-runs the checker.
"""
import os
import signal
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'tools', 'nghist'))

import nghist_prove as NP                                          # noqa: E402
import reachst_prove as RP                                         # noqa: E402

KNT = [(2, 2, 200, 40000), (3, 2, 200, 40000), (2, 3, 200, 40000),
       (3, 3, 200, 40000), (4, 2, 200, 40000), (2, 4, 200, 40000),
       (4, 3, 200, 40000), (3, 4, 200, 40000)]


class TO(Exception):
    pass


def _h(*a):
    raise TO()


signal.signal(signal.SIGALRM, _h)


def main():
    mstr = sys.argv[1]
    qext = sys.argv[2] if len(sys.argv) > 2 else 'D'
    budget = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    for (k, n, t, fuel) in KNT:
        try:
            signal.alarm(budget)
            res, err = RP.prove_ext(mstr, k, n, t, fuel, qext=qext)
            signal.alarm(0)
        except TO:
            signal.alarm(0)
            print('k=%d n=%d t=%d fuel=%d  TIMEOUT(%ds)' % (k, n, t, fuel, budget))
            sys.stdout.flush()
            continue
        if res is None:
            print('k=%d n=%d t=%d fuel=%d  MISS %s' % (k, n, t, fuel, err))
        else:
            print('k=%d n=%d t=%d fuel=%d  OK nctx=%d' % (k, n, t, fuel, res['nctx']))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
