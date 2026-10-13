#!/usr/bin/env python3
"""Partition every changed Coq target for CI; no proof results are cached.

The two existing integration-only exclusions remain in the full closeout job.
Renames are treated as delete/add so the new module path is checked too.
"""
import argparse
import hashlib
import json
import math
import subprocess

EXCLUDED = {'theories/CloseoutTr/CloseoutTr.v',
            'theories/CloseoutTr/RemainingTr.v'}


def changed(base):
    result = subprocess.run(
        ['git', 'diff', '--no-renames', '--name-only', '-z', '--diff-filter=AM',
         base + '...HEAD', '--', 'theories/*.v'],
        check=True, stdout=subprocess.PIPE)
    return sorted(p[:-2] + '.vo' for p in result.stdout.decode().split('\0')
                  if p and p not in EXCLUDED)


def partition(targets, count):
    if count < 1:
        raise ValueError('shard count must be positive')
    # Mix proof families, then deal equal counts to each runner. Stable across
    # Python versions and independent of process hash randomization.
    ordered = sorted(set(targets), key=lambda p: (hashlib.sha256(p.encode()).digest(), p))
    return [sorted(ordered[k::count]) for k in range(count)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True)
    parser.add_argument('--matrix', action='store_true')
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=1)
    args = parser.parse_args()
    targets = changed(args.base)
    if args.matrix:
        count = min(6, max(1, math.ceil(len(targets) / 600)))
        print(json.dumps({'include': [{'shard': k, 'shards': count}
                                      for k in range(count)]}))
    else:
        if not 0 <= args.shard < args.shards:
            parser.error('shard must be between zero and shards - 1')
        for target in partition(targets, args.shards)[args.shard]:
            print(target)


if __name__ == '__main__':
    main()
