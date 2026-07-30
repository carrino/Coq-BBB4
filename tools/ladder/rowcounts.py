#!/usr/bin/env python3
"""UNTRUSTED: every number LADDER_PLAN sec.4e quotes, printed from the sweeps.

A section that quotes measurements should be regenerable from the artefacts it
cites, so this is the only place the counts are computed and the prose copies
them rather than restating them.

Usage: rowcounts.py OLD.jsonl NEW.jsonl [NUMSYS.txt ...]
"""

import collections
import json
import os
import sys

from sweep import subbucket

HERE = os.path.dirname(os.path.abspath(__file__))


def load(p):
    return {json.loads(l)['spec']: json.loads(l) for l in open(p) if l.strip()}


def specs(f):
    return [l.split()[0] for l in open(os.path.join(HERE, f)) if l.strip()]


def main():
    old, new = load(sys.argv[1]), load(sys.argv[2])
    numsys = {}
    for p in sys.argv[3:]:
        for l in open(p):
            w = l.split()
            if len(w) > 3:
                numsys[w[0]] = w[3]
    both = [s for s in new if s in old]
    print('== headline ==')
    print('rows measured        %d' % len(both))
    print('closed before        %d' % sum(1 for s in both
                                          if old[s].get('closed')))
    print('closed after         %d' % sum(1 for s in both
                                          if new[s].get('closed')))
    print('\n== per working set ==')
    for name, f in [('engine-gap (c)', 'work24_enginegap.txt'),
                    ('two-parameter target', 'work71_twoparam.txt'),
                    ('register (rung 3)', 'work17_register.txt'),
                    ('regression (closed)', 'work21_closed.txt')]:
        ss = [s for s in specs(f) if s in new and s in old]
        o = sum(1 for s in ss if old[s].get('closed'))
        n = sum(1 for s in ss if new[s].get('closed'))
        print('%-22s %3d rows   %3d -> %3d  (%+d)' % (name, len(ss), o, n,
                                                      n - o))
    cl = [new[s] for s in both if new[s].get('closed')]
    print('\n== the closed certificates ==')
    print('closed                       %d' % len(cl))
    print('differential agrees          %d' % sum(1 for r in cl
                                                  if r.get('differential_ok')))
    print('exact predicted step counts  %d'
          % sum(1 for r in cl if r.get('differential_steps_ok')))
    print('>= 40 laps from blank        %d'
          % sum(1 for r in cl
                if (r.get('chain_check') or {}).get('laps_confirmed', 0) >= 40))
    print('never-QH (all states i.o.)   %d'
          % sum(1 for r in cl if r['liveness']['all_states']))
    print('quasi-halt witness named     %d'
          % sum(1 for r in cl if not r['liveness']['all_states']))
    print('median arms %d   max arms %d   median wall %.0fs'
          % (sorted(len(r['arms']) for r in cl)[len(cl) // 2],
             max(len(r['arms']) for r in cl),
             sorted(r.get('wall', 0) for r in cl)[len(cl) // 2]))
    print('\nfill law of the closed rows:')
    for k, n in collections.Counter((r.get('fill') or {}).get('law')
                                    for r in cl).most_common():
        print('   %-40s %3d' % (k, n))
    print('the hard-coded carry law would have sufficed on %d of %d'
          % (sum(1 for r in cl
                 if (r.get('fill') or {}).get('is_the_odometer_carry')),
             len(cl)))
    print('enumeration: %s'
          % dict(collections.Counter(r.get('enumeration') for r in cl)))
    print('two-parameter far side: %d'
          % sum(1 for r in cl if r.get('outer_parameter')))
    print('\nphases of the closed rows: %s'
          % dict(collections.Counter((r.get('phases') or {}).get('n', 1)
                                     for r in cl)))
    print('closed BY the phase pass (>1 terminator)  %d'
          % sum(1 for r in cl
                if (r.get('phases') or {}).get('found_by_the_phase_pass')))
    print('arm order is a subsumption linearization  %d of %d'
          % (sum(1 for r in cl
                 if r.get('arm_order_is_subsumption_linearization')), len(cl)))
    print('selection shadowed a correct later arm    %d'
          % sum(1 for r in cl if r.get('arm_selection_shadowed')))
    print('\n== transitions ==')
    t = collections.Counter((subbucket(old[s]), subbucket(new[s]))
                            for s in both)
    for (a, b), n in sorted(t.items(), key=lambda kv: -kv[1]):
        tag = '  GAIN' if (b == 'closed' and a != 'closed') else (
            '  LOSS' if (a == 'closed' and b != 'closed') else '')
        print('  %-34s -> %-34s %3d%s' % (a, b, n, tag))
    print('\n== after, by verdict ==')
    for k, n in collections.Counter(subbucket(new[s])
                                    for s in both).most_common():
        print('  %-36s %3d' % (k, n))
    print('\n== wall-clock capped (>= 295 s) ==')
    cap = [s for s in both if (new[s].get('wall') or 0) >= 295]
    print('  %d rows: %s' % (len(cap), ', '.join(sorted(cap)[:8])))
    if numsys:
        print('\n== number system at the busiest constant-far-side anchor ==')
        for setname, f in [('engine-gap (c)', 'work24_enginegap.txt'),
                           ('two-parameter target', 'work71_twoparam.txt'),
                           ('register (rung 3)', 'work17_register.txt'),
                           ('regression (closed)', 'work21_closed.txt')]:
            c = collections.Counter(numsys.get(s, 'unscanned')
                                    for s in specs(f))
            print('  %-22s %s' % (setname, dict(c)))
        fib = [s for s in both if numsys.get(s) == 'FIBONACCI']
        print('  FIBONACCI rows: %d; still open after: %d'
              % (len(fib), sum(1 for s in fib if not new[s].get('closed'))))


if __name__ == '__main__':
    main()
