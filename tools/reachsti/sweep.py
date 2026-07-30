#!/usr/bin/env python3
"""UNTRUSTED coverage sweep for the ReachStI tier.

Per row, per state, which engine can prove that state LIVE?

  reachsti   [Checkers/ReachStI.v]: the goal-avoiding sub-machine has a
             measure certificate over the invariant "state in allowed"
             (allowed = the largest total, closed state set -- on a
             [1RB---] row that drops [StA] and with it the undefined
             transition)
  closure    [tools/nghist] NGramHist at k in {2,3}, n in {2,3}: the
             abstraction's own liveness certificate

A row is BOARDABLE only when every allowed state is covered by one of the
two, because [NeverQuasiHaltsSt] (and the [QHBound] half of [iqh]) obliges
every visited state at once.

  python3 tools/reachsti/sweep.py <rowfile>

Nothing here carries proof weight.
"""
import os
import signal
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'tools', 'nghist'))

from cert_search import parse, allowed_set, search, LAB          # noqa: E402
import nghist_prove as NP                                        # noqa: E402

KN = [(2, 2), (3, 2), (2, 3)]


class TO(Exception):
    pass


def _h(*a):
    raise TO()


signal.signal(signal.SIGALRM, _h)


def closure_certs(m, alab, budget=45):
    out = set()
    tm = NP.decode(m)
    for (k, n) in KN:
        try:
            signal.alarm(budget)
            g = NP.grow(tm, k, n, 200, 40000)
            signal.alarm(0)
        except TO:
            signal.alarm(0)
            continue
        if g is None:
            continue
        seen, edges = g[3], g[4]
        for q in alab:
            if q in out:
                continue
            try:
                signal.alarm(budget)
                c = NP.cert_for_state(tm, seen, edges, q, n=n)
                signal.alarm(0)
            except TO:
                signal.alarm(0)
                continue
            if c is not None:
                out.add(q)
    return out


def main():
    rows = open(sys.argv[1]).read().split()
    full = 0
    for m in rows:
        tab = parse(m)
        allowed = allowed_set(tab)
        alab = [LAB[a] for a in allowed]
        rsi = {LAB[q] for q in allowed if search(m, q, allowed)}
        clo = closure_certs(m, alab)
        cov = rsi | clo
        ok = all(q in cov for q in alab)
        full += ok
        print('%s allowed=%-4s reachsti=%-4s closure=%-4s %s' % (
            m, ''.join(alab), ''.join(sorted(rsi)) or '-',
            ''.join(sorted(clo)) or '-',
            'BOARDABLE' if ok else
            'missing ' + ''.join(q for q in alab if q not in cov)))
        sys.stdout.flush()
    print('\n%d of %d rows have every allowed state covered' % (full, len(rows)))


if __name__ == '__main__':
    main()
