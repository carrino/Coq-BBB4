#!/usr/bin/env python3
"""Partition a transition-level collection-walk deferred list against the
state-level census tiers (UNTRUSTED bookkeeping -- burn-down targeting
only, no proof weight).

Buckets, in precedence order:

  proven      in the state Proven tier (kernel-proved NeverQuasiHaltsSt):
              per-instruction re-certification targets -- each either
              re-certifies never-QH at transition level or FLIPS to a
              score-bearing quasihalter (the champion-risk population);
  provenqh    in the state ProvenQH / RerootQH tiers (kernel-proved
              state-QH with QHBound 2000): wrap-route targets -- the
              state bound pins the machine's behavior, the instruction
              bound needs the 8-way re-scan;
  dcensus     in the frozen state D_census (27 holdouts + 5,129 residue):
              already-hard at state level, expect the same routes that
              boarded them (ReachSt / Ladder / counters) per instruction;
  partial     the row has undefined slots (a TNF interior node the walk
              deferred): decided per-orbit through completion, usually
              alongside its full-machine extensions;
  inwalk      none of the above: machines the STATE census decided
              in-walk (n-gram / rank / wrapped-QHBound / RepWL tiers)
              whose per-instruction verdicts are simply not built yet --
              the phase-3 tier ports should re-absorb the bulk of these
              at re-walk time without any per-machine work.

Usage: classify_deferred.py DEFERRED [--outdir DIR]
  DEFERRED  decoded machine-text list (one per line) or raw collect .out
  --outdir  also write one file per bucket (default: counts only)

Tier text lists are read from tools/censustr/state_tiers/*.txt (emitted
by extract_state_tiers, see that directory's README) and
tools/census_holdouts_kept.txt + tools/census_residue.txt.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_deferredtr import read_machines  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def read_list(path):
    out = set()
    with open(path) as f:
        for line in f:
            s = line.strip()
            if s and not s.startswith('#'):
                out.add(s)
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    outdir = None
    if '--outdir' in sys.argv:
        outdir = sys.argv[sys.argv.index('--outdir') + 1]
    machines = read_machines(args[0])

    tiers = os.path.join(HERE, 'state_tiers')
    proven = read_list(os.path.join(tiers, 'proven.txt'))
    provenqh = read_list(os.path.join(tiers, 'provenqh.txt'))
    provenqh |= read_list(os.path.join(tiers, 'rerootqh.txt'))
    dcensus = read_list(os.path.join(REPO, 'tools', 'census_holdouts_kept.txt'))
    dcensus |= read_list(os.path.join(REPO, 'tools', 'census_residue.txt'))

    buckets = {k: [] for k in
               ('proven', 'provenqh', 'dcensus', 'partial', 'inwalk')}
    for m in machines:
        if m in proven:
            buckets['proven'].append(m)
        elif m in provenqh:
            buckets['provenqh'].append(m)
        elif m in dcensus:
            buckets['dcensus'].append(m)
        elif '---' in m:
            buckets['partial'].append(m)
        else:
            buckets['inwalk'].append(m)

    total = len(machines)
    print(f'total deferred: {total}')
    for k in ('proven', 'provenqh', 'dcensus', 'partial', 'inwalk'):
        n = len(buckets[k])
        print(f'  {k:9} {n:8}  ({100.0 * n / max(total, 1):5.1f}%)')
    if outdir:
        os.makedirs(outdir, exist_ok=True)
        for k, rows in buckets.items():
            with open(os.path.join(outdir, f'deferred_{k}.txt'), 'w') as f:
                f.write('\n'.join(rows) + ('\n' if rows else ''))
        print(f'per-bucket lists written to {outdir}', file=sys.stderr)


if __name__ == '__main__':
    main()
