#!/usr/bin/env python3
"""UNTRUSTED: two sweeps, one table.

The point of the split is that the ENGINE-GAP pass and the two-parameter
constructor must be measured apart -- one is bug-fixing, the other is
mathematics, and a single headline number would let either take credit for the
other's rows.  So every count here is reported per working set:

    work24_enginegap.txt  the (c) rows: arm lands off, interior not covered,
                          no signal in the bucket where sisters closed
    work71_twoparam.txt   the non-register overflow rows
    work17_register.txt   the rung-three rows -- expected to stay open
    work21_closed.txt     the regression set -- expected to stay closed
"""

import collections
import json
import os
import sys

from sweep import subbucket

HERE = os.path.dirname(os.path.abspath(__file__))
SETS = [('engine-gap (c)', 'work24_enginegap.txt'),
        ('two-parameter target', 'work71_twoparam.txt'),
        ('register (rung 3)', 'work17_register.txt'),
        ('regression: closed', 'work21_closed.txt')]


def load(p):
    return {json.loads(l)['spec']: json.loads(l) for l in open(p) if l.strip()}


def main():
    old, new = load(sys.argv[1]), load(sys.argv[2])
    both = [s for s in new if s in old]
    print('rows in both sweeps: %d\n' % len(both))
    print('%-24s %5s %8s %8s %7s' % ('working set', 'rows', 'closed<-',
                                     'closed->', 'delta'))
    tot_o = tot_n = 0
    for name, f in SETS:
        specs = [l.split()[0] for l in open(os.path.join(HERE, f))
                 if l.strip()]
        specs = [s for s in specs if s in new and s in old]
        o = sum(1 for s in specs if old[s].get('closed'))
        n = sum(1 for s in specs if new[s].get('closed'))
        tot_o, tot_n = tot_o + o, tot_n + n
        print('%-24s %5d %8d %8d %+7d' % (name, len(specs), o, n, n - o))
    print('%-24s %5d %8d %8d %+7d' % ('TOTAL (listed)', 0, tot_o, tot_n,
                                      tot_n - tot_o))
    print('\nall rows: closed %d -> %d of %d'
          % (sum(1 for s in both if old[s].get('closed')),
             sum(1 for s in both if new[s].get('closed')), len(both)))
    print('\nverdict transitions (before -> after):')
    t = collections.Counter((subbucket(old[s]), subbucket(new[s]))
                            for s in both)
    for (a, b), n in sorted(t.items(), key=lambda kv: -kv[1]):
        flag = '' if a == b else ('  <== GAIN' if b == 'closed'
                                  else ('  <== LOSS' if a == 'closed' else ''))
        print('  %-34s -> %-34s %3d%s' % (a, b, n, flag))
    print('\nafter, by verdict:')
    for k, n in collections.Counter(subbucket(new[s])
                                    for s in both).most_common():
        print('  %-36s %3d' % (k, n))
    cl = [new[s] for s in both if new[s].get('closed')]
    if cl:
        print('\nclosed: %d; differential ok %d; exact step counts %d; '
              '>=40 laps %d; never-QH %d'
              % (len(cl), sum(1 for r in cl if r.get('differential_ok')),
                 sum(1 for r in cl if r.get('differential_steps_ok')),
                 sum(1 for r in cl
                     if (r.get('chain_check') or {}).get('laps_confirmed', 0)
                     >= 40),
                 sum(1 for r in cl if r['liveness']['all_states'])))
        fl = collections.Counter(
            (r.get('fill') or {}).get('law', '?') for r in cl)
        print('closed, by fill law:')
        for k, n in fl.most_common():
            print('   %-44s %3d' % (k, n))
        print('closed, by enumeration: %s'
              % dict(collections.Counter(r.get('enumeration') for r in cl)))
        print('closed, two-parameter far side: %d'
              % sum(1 for r in cl if r.get('outer_parameter')))
        print('closed: median arms %d, median wall %.0fs'
              % (sorted(len(r['arms']) for r in cl)[len(cl) // 2],
                 sorted(r.get('wall', 0) for r in cl)[len(cl) // 2]))
    w = sorted((new[s].get('wall', 0) for s in both), reverse=True)
    print('wall: total %.0fs  max %.0fs  median %.0fs'
          % (sum(w), w[0], w[len(w) // 2]))


if __name__ == '__main__':
    main()
