#!/usr/bin/env python3
"""Order pending instruction-walk files using optional scheduling hints.

Read one pending filename per stdin line and emit the same filenames, once
per input occurrence. Proof contents, freshness checks and parallelism are
outside this tool. Missing or invalid profiles, or a different unit count,
fall back to lexical order. Unknown units run first, then known units from
longest estimate to shortest; filename order breaks ties deterministically.
"""
import argparse
import json
import math
from pathlib import Path
import sys


def read_costs(path, units):
    data = json.loads(Path(path).read_text())
    if not isinstance(data, dict) or type(data.get('units')) is not int:
        raise ValueError('profile must declare its unit count')
    if data['units'] != units:
        raise ValueError(f"profile has {data['units']} units, requested {units}")
    costs = data.get('seconds')
    if not isinstance(costs, dict):
        raise ValueError('profile must contain a seconds dictionary')
    names = {f'UnitTr_{i:02d}' for i in range(units)}
    for name, seconds in costs.items():
        if name not in names:
            raise ValueError(f'profile contains an invalid unit name: {name}')
        if (isinstance(seconds, bool) or not isinstance(seconds, (int, float))
                or not math.isfinite(seconds) or seconds < 0):
            raise ValueError(f'profile has an invalid estimate for {name}')
    return costs


def ordered_paths(paths, costs):
    def priority(path):
        name = Path(path).stem
        if name not in costs:
            return (0, 0, path)
        return (1, -costs[name], path)
    return sorted(paths, key=priority)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--profile', type=Path,
                    default=Path(__file__).with_name('walk_costs.json'))
    ap.add_argument('--units', type=int, required=True)
    args = ap.parse_args(argv)
    if args.units < 1:
        ap.error('--units must be positive')
    paths = [line for line in sys.stdin.read().splitlines() if line]
    try:
        costs = read_costs(args.profile, args.units)
    except (OSError, ValueError) as error:
        print(f'walk ordering: using lexical order ({error})', file=sys.stderr)
        costs = {}
    result = ordered_paths(paths, costs)
    if result:
        sys.stdout.write('\n'.join(result) + '\n')


if __name__ == '__main__':
    main()
