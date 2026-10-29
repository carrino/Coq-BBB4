"""Find new two-prefix conjugacy candidates from an audited burndown inventory.

This is discovery only: exact finite tape comparison confirms native hash hits,
but every source theorem, transport, completion and census obligation still
needs Coq replay. Generated candidate lists and native logs remain ignored.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import time

import group_families as grouping
from check_conjugate_batch import exact_config

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matches(known, targets, swap):
    full, partial = {}, {}
    for row in known:
        table = grouping.parse(row['machine'])
        mask = grouping.defined_mask(table)
        if mask == 255:
            full[table] = row
        else:
            key = tuple(cell for i, cell in enumerate(table) if mask >> i & 1)
            partial.setdefault(mask, {})[key] = row
    hits = []
    for machine in targets:
        table = grouping.parse(machine)
        found = None
        for perm in grouping.PERMS:
            for mirror in (False, True):
                transformed = grouping.rename(table, perm, mirror=mirror, swap=swap)
                if transformed[0] not in ('0LB', '1LB'):
                    continue
                row = full.get(transformed)
                available = grouping.defined_mask(transformed)
                if row is None:
                    for mask, pool in partial.items():
                        if mask & ~available:
                            continue
                        row = pool.get(tuple(cell for i, cell in enumerate(transformed) if mask >> i & 1))
                        if row is not None:
                            break
                if row is not None:
                    found = dict(machine=machine, source=row['machine'],
                                 methods=row['methods'], bound=int(row['instruction_bound']),
                                 perm=perm, mirror=mirror)
                    break
            if found is not None:
                break
        if found is not None:
            hits.append(found)
    return hits


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--burndown', type=Path, default=ROOT/'research/next-burndown-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/burn2-conjugate-search')
    parser.add_argument('--fuel', type=int, default=4096)
    parser.add_argument('--max-source-bound', type=int, default=131072)
    parser.add_argument('--native-timeout', type=int, default=120)
    args = parser.parse_args()
    if not 1 <= args.fuel <= 1000000 or args.native_timeout < 1:
        raise ValueError('Positive bounded fuel and timeout required')
    output = args.output_dir.resolve()
    if not output.is_relative_to(ROOT/'build'):
        raise ValueError('Discovery output must stay under ignored four/build')
    output.mkdir(parents=True, exist_ok=True)
    report_hash = sha(args.burndown)
    report = json.loads(args.burndown.read_text())
    pins = {str(args.burndown.resolve()): report_hash}

    def artifact(name):
        spec = report['outputs'][name]
        path = (ROOT/spec['path']).resolve()
        if not path.is_relative_to(ROOT) or sha(path) != spec['sha256']:
            raise ValueError('Burndown artifact differs: ' + name)
        pins[str(path)] = spec['sha256']
        return path

    known = list(csv.DictReader(artifact('both-families.tsv').open(), delimiter='\t'))
    known = [row for row in known if int(row['instruction_bound']) <= args.max_source_bound]
    targets = artifact('both-remaining.txt').read_text().splitlines()
    queue = {row['machine'] for row in csv.DictReader(artifact('queued.tsv').open(), delimiter='\t')}
    state = set(artifact('state-remaining.txt').read_text().splitlines())
    started = time.monotonic()
    plain = matches(known, targets, False)
    all_swapped = matches(known, targets, True)
    swapped = [row for row in all_swapped if row['machine'] not in queue]
    candidates = output/'candidates.txt'
    candidates.write_text(''.join(row['machine']+'\n' for row in swapped))
    (output/'table-witnesses.json').write_text(json.dumps(swapped, indent=2)+'\n')
    probe_source = ROOT/'tools/conjugate_probe.cpp'
    pins[str(probe_source)] = sha(probe_source)
    binary = output/'conjugate_probe'
    subprocess.run(['g++', '-O2', '-std=c++17', str(probe_source), '-o', str(binary)], check=True, timeout=60)
    with (output/'probe.tsv').open('w') as stream:
        subprocess.run([str(binary), str(args.fuel), str(candidates)], stdout=stream,
                       check=True, timeout=args.native_timeout)
    probe = list(csv.DictReader((output/'probe.tsv').open(), delimiter='\t'))
    if [row['machine'] for row in probe] != [row['machine'] for row in swapped]:
        raise ValueError('Native result inventory differs')
    by_machine = {row['machine']: row for row in swapped}
    hits = []
    for row in probe:
        if row['status'] != 'match':
            continue
        destination, origin = int(row['target_boot']), int(row['source_boot'])
        machine = row['machine']
        if exact_config(machine, 0, destination) != exact_config(machine, 1, origin):
            raise ValueError('Native hash hit failed exact configuration comparison')
        hits.append({**by_machine[machine], 'target_boot':destination, 'source_boot':origin})
    for name, expected in pins.items():
        if sha(Path(name)) != expected:
            raise ValueError('Input changed during search: ' + name)
    (output/'exact-hits.json').write_text(json.dumps(hits, indent=2)+'\n')
    result = dict(scope='Search candidates only; zero new kernel-audited obligations in this report.',
                  burndown_report_sha256=report_hash, source_bound_limit=args.max_source_bound,
                  ordinary_table_matches=len(plain), swapped_table_matches=len(all_swapped),
                  queued_overlap_excluded=len(all_swapped)-len(swapped), probed=len(swapped),
                  fuel=args.fuel, statuses=dict(Counter(r['status'] for r in probe)),
                  exact_matches=len(hits), state_obligation_candidates=sum(r['machine'] in state for r in hits),
                  source_methods=dict(Counter(r['methods'] for r in hits)),
                  input_sha256=pins, seconds=round(time.monotonic()-started,3))
    (output/'search-summary.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'input_sha256'}, indent=2))


if __name__ == '__main__':
    main()
