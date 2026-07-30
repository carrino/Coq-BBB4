#!/usr/bin/env python3
"""UNTRUSTED sweep: which closeout-residue rows are QUASIHALTERS the capped
`t` search missed?

`sweep_qhbound_residue.py` searches `CAND_T = (64, 256, 1024)`.  Wave-32 found
`1RB1RD_1RC0LD_1LB0RA_1LC0LC` in the residue whose quiet state's last visit is
at index **2331** -- every candidate `t` was below the one index that had to be
exceeded, so the route never fired, and the row sat behind never-quasihalting
emitters for thirty-two waves under a gate label that was true and useless.

This runs the SAME gate (`Checkers/Wrap.ngram_check_qhbound`: wrap the quiet
state to a halt, close the n-gram abstraction at index `t`, require the closure
halt-free and per-state acyclic) over the current open list, with `t` taken from
each machine's own MEASURED last-visit index rather than from a fixed list.

For every state `q` it simulates far enough to see whether `q` stops firing, and
if it does, tries `t` just past that index.  A state still firing at the horizon
is not a candidate.  Nothing here is a certificate: `gen_qhb_row.py` renders the
board and the kernel re-runs the check.

Usage
  sweep_qhbound_deep.py [ROWS] [--horizon N] [--out TSV]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import bulk_prover as bp                                           # noqa: E402
import sweep_qhbound_residue as S                                  # noqa: E402

LAB = 'ABCD'
CAND_N = (2, 3, 4, 5, 6)


def last_visits(tbl, horizon):
    """{state: last index it is visited at} over `horizon` steps, plus the set
    still firing in the final decile (so not eventually quiet)."""
    tape, pos, q = {}, 0, 0
    last = {0: 0}
    for i in range(horizon):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return last, set(), i                     # halts: not our business
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
        last[q] = i + 1
    live = {s for s, ix in last.items() if ix > horizon - horizon // 10}
    return last, live, None


def find(m, horizon):
    """(q, s, n, t) for a QHBound cert whose `t` is read off the machine."""
    tbl = bp.parse(m)
    last, live, halted = last_visits(tbl, horizon)
    if halted is not None:
        return None
    for qq, s in sorted(last.items(), key=lambda kv: kv[1]):
        if qq in live:
            continue                       # still firing: not eventually quiet
        for t in (s + 69, s + 256, s + 1024):
            for n in CAND_N:
                r = S.wrapped_closure(tbl, qq, n, t)
                if r is None or not S.live_ok(*r):
                    continue
                return (qq, s, n, t)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows', nargs='?',
                    default=os.path.join(HERE, 'closeout', 'core_rows.txt'))
    ap.add_argument('--horizon', type=int, default=200000)
    ap.add_argument('--out')
    a = ap.parse_args()
    specs = [x.split()[0] for x in open(a.rows) if x.strip()
             and not x.startswith('#')]
    hits = []
    for i, m in enumerate(specs):
        try:
            r = find(m, a.horizon)
        except Exception as e:                                      # noqa: BLE001
            print('%4d/%d %-30s ERR %s' % (i + 1, len(specs), m, e))
            continue
        if r is None:
            continue
        qq, s, n, t = r
        hits.append((m, LAB[qq], s, n, t))
        print('%4d/%d %-30s QUASIHALTER: quiet %s last visit %d, n=%d t=%d '
              '-> QHBound %d' % (i + 1, len(specs), m, LAB[qq], s, n, t, t + 1))
    print('\n%d of %d open rows are QHBound-decidable with t read off the '
          'machine' % (len(hits), len(specs)))
    if a.out:
        with open(a.out, 'w') as f:
            f.write('machine\tquiet_state\ts\tn\tt\n')
            for row in hits:
                f.write('\t'.join(str(x) for x in row) + '\n')
        print('->', a.out)
    return 0


if __name__ == '__main__':
    sys.exit(main())
