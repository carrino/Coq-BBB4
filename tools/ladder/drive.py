#!/usr/bin/env python3
"""UNTRUSTED driver: mine a trace, build a ladder, report what it looks like
and where closure stalls.  Stage-A instrumentation, not a decider yet.

Usage: drive.py --spec SPEC [--steps N] [--verbose]
       drive.py --list FILE [--steps N]
"""

import argparse
import sys

from engine import MARKER, parse_tm
from trace import simulate
from discover import mine_shapes, build_ladder, coverage


def analyze(spec, steps=30000, verbose=False):
    tm = parse_tm(spec)
    snaps = simulate(tm, steps)
    if snaps and snaps[-1][1] is None:
        return {'spec': spec, 'verdict': 'halt'}
    table = mine_shapes(snaps)
    rules = build_ladder(tm, table, verbose=verbose)
    from validate import check_ladder
    bad = check_ladder(tm, rules)
    hits, tot = coverage(rules, snaps)
    nlocal = sum(1 for ru in rules
                 if any(w == MARKER for w, _ in ru.lhs[2] + ru.lhs[3]))
    r = {'spec': spec, 'verdict': 'ladder', 'shapes': len(table),
         'rules': len(rules), 'local': nlocal,
         'levels': max((ru.level for ru in rules), default=-1) + 1,
         'rule_states': ''.join(sorted(set(
             'ABCD'[tr[0]] for ru in rules for tr in ru.fired))),
         'cover': '%d/%d' % (hits, tot),
         'invalid': bad}
    if verbose:
        for ru in rules:
            print('  %r' % ru)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--list')
    ap.add_argument('--steps', type=int, default=30000)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.strip() for l in open(a.list) if l.strip()]
    for spec in specs:
        r = analyze(spec, a.steps, a.verbose)
        print('%-30s %s' % (spec, {k: v for k, v in r.items()
                                   if k != 'spec'}))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
