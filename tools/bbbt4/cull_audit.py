#!/usr/bin/env python3
"""UNTRUSTED audit of the harness's hardest machines against BBB_tr(4).

The BBB harness's champion hunt (carrino/BBB results/champhunt/cull.csv)
left 432 machines undecided at 10^10 steps: rare-fire counters whose
quietest instruction had last fired billions of steps in, the shape that
made SCOPING_INSTR.md section 2 expect a value far above 32,779,478.
This script answers two questions about each of them:

  1. COVERAGE: which kernel-checked object settles it?
     - a closeout batch (closeouttr_boarded.tsv: a deferred row h with
       h <= m, i.e. m completes h), or
     - the census's proven tiers (prov_tr / provqh_tr specs, read by
       tools/censustr/proven_specs.py), or
     - neither: the walk's own decider settled it inside census_tr
       (cyclers, translated cyclers, RepWL, ... run in the kernel).
  2. PREDICTION: bbbt4_bound says no instruction is quiet after a last
     fire at index >= 32,779,478, so every instruction that fired at or
     past that index must fire again after any horizon.  refire.c checks
     this on concrete runs; this script reads its output.

Usage: cull_audit.py CULL_CSV REFIRE_OUT... [--tsv OUT.tsv]
Neither part is evidence the kernel needs; the theorem stands without
them.  They are cross-checks a reader can rerun in minutes. """
import argparse
import csv
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'censustr'))
import proven_specs  # noqa: E402

B = 32779478


def ents(s):
    t = s.replace('_', '')
    return [t[i:i + 3] for i in range(0, len(t), 3)]


def le(h, m):
    """h <= m: every defined entry of h agrees with m."""
    return all(a == '---' or a == b for a, b in zip(ents(h), ents(m)))


def parse_refire(paths):
    out = {}
    for p in paths:
        for line in open(p):
            f = line.split()
            if len(f) < 4:
                continue
            m, verdict, last_step = f[0], f[-2], int(f[-1])
            checked, nexts = 0, []
            for tok in f[2:-2]:
                parts = tok.split(':')
                if len(parts) == 4:
                    checked += 1
                    if parts[3] != '-':
                        nexts.append(int(parts[3]))
            horizon = int(f[1].split('=')[1])
            out[m] = (verdict, horizon, checked, max(nexts) if nexts else 0, last_step)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cull')
    ap.add_argument('refire', nargs='*')
    ap.add_argument('--tsv')
    a = ap.parse_args()

    boarded = [l.rstrip('\n').split('\t')
               for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv'))]
    proven = sorted(proven_specs.proven())
    rows = list(csv.DictReader(open(a.cull)))
    rf = parse_refire(a.refire)

    cov, tags, verdicts = Counter(), Counter(), Counter()
    checked = refired = 0
    latest = (0, '')
    out = []
    for r in rows:
        m = r['machine']
        hb = sorted({b for h, b in boarded if le(h, m)})
        hp = [h for h in proven if le(h, m)]
        if hb:
            kind, by = 'closeout', ','.join(hb)
            for b in hb:
                tags[b.rsplit('_', 1)[0]] += 1
        elif hp:
            kind, by = 'proven-tier', hp[0]
        else:
            kind, by = 'census-walk', '-'
        cov[kind] += 1
        v = rf.get(m)
        if v:
            verdicts[v[0]] += 1
            checked += v[2]
            if v[0] == 'OK':
                refired += v[2]
            if v[3] > latest[0]:
                latest = (v[3], m)
        out.append((m, kind, by) + (tuple(map(str, v)) if v else ('-',) * 5))

    print('machines: %d' % len(rows))
    print('coverage: ' + ', '.join('%s %d' % kv for kv in cov.most_common()))
    print('closeout tags: ' + ', '.join('%s %d' % kv for kv in tags.most_common()))
    if rf:
        print('refire verdicts: ' + ', '.join('%s %d' % kv for kv in verdicts.most_common()))
        print('instructions predicted to fire again: %d, fired again: %d' % (checked, refired))
        print('latest refire: step %d (%s)' % latest)
    if a.tsv:
        with open(a.tsv, 'w') as f:
            f.write('machine\tcovered_by\tobject\trefire\thorizon\tinstrs_checked\tlast_refire\tsteps_run\n')
            for t in out:
                f.write('\t'.join(t) + '\n')


if __name__ == '__main__':
    main()
