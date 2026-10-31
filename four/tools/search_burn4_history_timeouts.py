"""Retry only frozen instruction-history timeouts at an eight-second budget.

Pilot and continuation slices are deterministic and disjoint. Completed native
rejections remain separate. Native successes still require independent Coq
replay; no earlier search or proof artifact is modified.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import resource
import subprocess

from check_campaign import read_inventory
from check_closure_wave import machine_hash, validate_row
from search_burn3_history_instructions import exact, read_results, sha

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn4-history-timeout8'
PREFIX = ROOT / 'research/burn4-history-timeout8'
INPUT = PREFIX.with_name(PREFIX.name + '-input.json')
PROBE = ROOT / 'build/wave3/driver-v2/probe'


def save(path, value):
    exact(path, json.dumps(value, indent=2, sort_keys=True) + '\n')


def prepare():
    paths = [ROOT / 'research' / name for name in (
        'burn3-history-instruction-search.json', 'burn3-history-instruction-plan.json',
        'burn3-history-instruction-checked.json', 'burn3-history-instruction-machines.json',
        'campaign-final-input.json', 'burn3-campaign-input.json')]
    sources = {str(path.relative_to(ROOT)): sha(path) for path in paths}
    old, plan, checked, inventory, baseline, supplement = [json.loads(path.read_text()) for path in paths]
    if old['plan_sha256'] != sha(paths[1]):
        raise ValueError('Previous native plan changed')
    original = [row for group in plan['groups'] for row in group['rows']]
    native = [row for group in old['results'] for row in group['rows']]
    if len(original) != 378 or len(native) != 378 or len({r['machine'] for r in original}) != 378:
        raise ValueError('Incomplete previous input/results')
    if [r['machine'] for r in original] != [r['machine'] for r in native]:
        raise ValueError('Previous result order differs')
    statuses = Counter(row['status'] for row in native)
    if dict(statuses) != old['statuses'] or statuses != Counter(candidate=160, rejected=80, timeout=138):
        raise ValueError('Unexpected previous native status partition')
    accepted_native = {row['machine'] for row in native if row['status'] == 'candidate'}
    if (accepted_native != {row['machine'] for row in inventory['rows']} or
        checked['checked_instruction_families'] != 160 or
        checked['inventory_sha256'] != sha(paths[3])):
        raise ValueError('Previous native successes do not match the audited inventory')
    accepted = set()
    for manifest in (baseline, supplement):
        for board in manifest['boards']:
            if board['scope'] == 'both':
                for spec in board['inventories']:
                    path = ROOT / spec['path']
                    sources[str(path.relative_to(ROOT))] = sha(path)
                    accepted.update(read_inventory(spec))
    timeouts = {row['machine'] for row in native if row['status'] == 'timeout'}
    rejected = sorted(row['machine'] for row in native if row['status'] == 'rejected')
    rows = sorted((row for row in original if row['machine'] in timeouts - accepted), key=machine_hash)
    for row in rows:
        validate_row(row)
        if row['mode'] != 'hist' or row['bound'] != 4096:
            raise ValueError('Unexpected history certificate parameters')
    if len(rows) != 138 or timeouts & accepted:
        raise ValueError('Expected all138 timeout rows still instruction-open')
    for path in (Path(__file__), ROOT / 'tools/search_burn3_history_instructions.py',
                 ROOT / 'tools/advanced_probe_v2.ml', PROBE):
        sources[str(path.relative_to(ROOT))] = sha(path)
    value = dict(scope='Scheduling only: timeout retry, no kernel proof claim.',
        sources_sha256=sources, original_timeout_rows=138, selected_rows=len(rows),
        excluded_accepted_timeout_ids=sorted(timeouts & accepted),
        completed_rejection_ids=rejected, previously_audited_native_successes=160,
        rows=rows, ordering='Ascending SHA256(machine UTF-8)',
        pilot_start=0, pilot_limit=16, continuation_start=16,
        timeout_seconds=8, workers=1, address_space_bytes=2147483648)
    if any(sha(ROOT / name) != digest for name, digest in sources.items()):
        raise ValueError('Selection source changed')
    save(INPUT, value)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--batch', choices=('pilot', 'rest'), default='pilot')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    data = prepare()
    if args.prepare:
        print(json.dumps(dict(selected_rows=data['selected_rows'], completed_rejections=80)))
        return
    if args.batch == 'rest':
        pilot = json.loads(PREFIX.with_name(PREFIX.name + '-pilot-search.json').read_text())
        if not pilot['candidate_rows'] or pilot['input_sha256'] != sha(INPUT):
            raise ValueError('Continuation requires a successful frozen pilot')
    rows = data['rows'][:16] if args.batch == 'pilot' else data['rows'][16:]
    directory = BASE / args.batch; directory.mkdir(parents=True, exist_ok=True)
    groups = {}
    for row in rows:
        key = tuple(row[k] for k in ('size', 'anchor', 'fuel', 'extra', 'history', 'bound'))
        groups.setdefault(key, []).append(row)
    by_machine, ledger_pins = {}, {}
    for index, (parameters, group) in enumerate(sorted(groups.items())):
        result_path = directory / f'group-{index:02d}.tsv'
        found = read_results(result_path)
        if [row['machine'] for row in found] != [row['machine'] for row in group[:len(found)]]:
            raise ValueError('Native result is not an exact input prefix')
        pending = group[len(found):]
        if pending and args.check:
            raise ValueError('Incomplete native retry ledger')
        if pending:
            input_path = directory / f'group-{index:02d}-pending-{len(found):04d}.txt'
            exact(input_path, ''.join(row['machine'] + '\n' for row in pending))
            size, anchor, fuel, extra, history, bound = parameters
            command = [str(PROBE), 'hist', str(bound), str(size), str(anchor), str(fuel),
                       str(extra), str(history), '8', str(input_path)]
            with result_path.open('a') as out, (directory / f'group-{index:02d}.log').open('a') as log:
                subprocess.run(command, stdout=out, stderr=log, check=True,
                               timeout=8 * len(pending) + 30)
            found = read_results(result_path)
        if [row['machine'] for row in found] != [row['machine'] for row in group]:
            raise ValueError('Incomplete native result inventory')
        by_machine.update((row['machine'], row) for row in found)
        ledger_pins[str(result_path.relative_to(ROOT))] = sha(result_path)
    results = [by_machine[row['machine']] for row in rows]
    candidates = [row for row in rows if by_machine[row['machine']]['status'] == 'candidate']
    if any(sha(ROOT / name) != digest for name, digest in data['sources_sha256'].items()):
        raise ValueError('Frozen dependency changed during retry')
    report = dict(scope='Native candidate discovery only; no proof claims.', batch=args.batch,
        input_sha256=sha(INPUT), selected_rows=len(rows), candidate_rows=len(candidates),
        candidates=candidates, statuses=dict(Counter(row['status'] for row in results)),
        results=results, ledger_sha256=ledger_pins, timeout_seconds=8,
        selection_start=0 if args.batch == 'pilot' else 16, workers=1)
    save(PREFIX.with_name(PREFIX.name + '-' + args.batch + '-search.json'), report)
    print(json.dumps({k: report[k] for k in ('batch', 'selected_rows', 'candidate_rows', 'statuses')}), flush=True)


if __name__ == '__main__':
    main()
