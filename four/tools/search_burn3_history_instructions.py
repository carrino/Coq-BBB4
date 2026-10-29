"""Try the frozen state-history certificates with the instruction checker.

The same per-row history parameters are passed to AdvancedPipeline in its
both-bound mode. Native acceptance is only discovery; every success needs
separate Coq replay. State proof files are never changed.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import resource
import subprocess
from types import SimpleNamespace

import check_state_pipeline_batch as state

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn3-history-instruction'
INPUT = ROOT / 'research/burn3-history-proof-input.json'
PLAN = ROOT / 'research/burn3-history-instruction-plan.json'
REPORT = ROOT / 'research/burn3-history-instruction-search.json'
PROBE = ROOT / 'build/wave3/driver-v2/probe'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def save(path, value):
    exact(path, json.dumps(value, indent=2, sort_keys=True) + '\n')


def selection():
    data, groups = state.load(SimpleNamespace(input=INPUT))
    search_path = ROOT / data['source_report']
    search = json.loads(search_path.read_text())
    candidates_path = ROOT / 'build/burn3-history/candidates.tsv'
    if sha(candidates_path) != search['candidate_tsv_sha256']:
        raise ValueError('Frozen state candidate TSV differs')
    with candidates_path.open() as stream:
        original = list(csv.DictReader(stream, delimiter='\t'))
    by_machine = {row['machine']: row for row in original}
    selected = []
    for group in groups:
        parameters = group['certificate']
        if parameters['mode'] != 'hist':
            raise ValueError('Expected history certificates')
        rows = []
        for packed in group['rows']:
            machine = state.unpack(packed)
            row = dict(machine=machine, bound=data['state_bound'], **parameters)
            saved = by_machine[machine]
            if any(saved[key] != str(value) for key, value in row.items()):
                raise ValueError('Native state result and compact input differ')
            rows.append(row)
        selected.append(dict(stage=group['stage'], parameters=parameters, rows=rows))
    count = sum(len(group['rows']) for group in selected)
    if count != data['selected_rows'] or count != len(original) or len(by_machine) != count:
        raise ValueError('Incomplete or duplicate state input')
    sources = {str(p.relative_to(ROOT)): sha(p) for p in
               (INPUT, search_path, candidates_path, PROBE, Path(__file__),
                ROOT / 'tools/advanced_probe_v2.ml', ROOT / 'tools/check_state_pipeline_batch.py')}
    return dict(scope='Untrusted instruction-upgrade search over frozen state candidates.',
                source_sha256=sources, selected_rows=count, groups=selected,
                workers=1, row_timeout_seconds=2, memory_bytes=2147483648,
                instruction_mode='hn_check_mode false'), selected


def read_results(path):
    if not path.exists():
        return []
    rows = []
    for line in path.read_text().splitlines():
        machine, status, seconds = line.split('\t')
        if status not in ('candidate', 'rejected', 'timeout', 'stack_overflow'):
            raise ValueError('Unknown native result')
        rows.append(dict(machine=machine, status=status, seconds=float(seconds)))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    plan, groups = selection()
    BASE.mkdir(parents=True, exist_ok=True)
    save(PLAN, plan)
    if args.prepare:
        print(json.dumps(dict(selected_rows=plan['selected_rows'], groups=len(groups))), flush=True)
        return
    results, accepted, statuses, ledger_pins = [], [], Counter(), {}
    for index, group in enumerate(groups):
        rows = group['rows']; parameters = group['parameters']
        output_path = BASE / f'stage-{index:02d}.tsv'
        current = read_results(output_path)
        if [r['machine'] for r in current] != [r['machine'] for r in rows[:len(current)]]:
            raise ValueError('Native ledger is not an exact input prefix')
        pending = rows[len(current):]
        if pending and args.check:
            raise ValueError('Incomplete native search ledger')
        if pending:
            input_path = BASE / f'stage-{index:02d}-pending-{len(current):04d}.txt'
            exact(input_path, ''.join(row['machine'] + '\n' for row in pending))
            command = [str(PROBE), 'hist', str(rows[0]['bound']), str(parameters['size']),
                       str(parameters['anchor']), str(parameters['fuel']), str(parameters['extra']),
                       str(parameters['history']), '2', str(input_path)]
            with output_path.open('a') as out, (BASE / f'stage-{index:02d}.log').open('a') as log:
                subprocess.run(command, stdout=out, stderr=log, check=True,
                               timeout=2 * len(pending) + 30)
            current = read_results(output_path)
        if [r['machine'] for r in current] != [r['machine'] for r in rows]:
            raise ValueError('Incomplete native result inventory')
        for row, result in zip(rows, current):
            statuses[result['status']] += 1
            if result['status'] == 'candidate':
                accepted.append(row)
        ledger_pins[str(output_path.relative_to(ROOT))] = sha(output_path)
        results.append(dict(stage=group['stage'], rows=current))
        print(json.dumps(dict(stage=group['stage'], attempted=sum(statuses.values()),
                              candidates=len(accepted), statuses=dict(statuses))), flush=True)
    if any(sha(ROOT / name) != digest for name, digest in plan['source_sha256'].items()):
        raise ValueError('Frozen state evidence changed during instruction search')
    save(REPORT, dict(scope='Native discovery only; zero kernel proof claims.',
        plan_sha256=sha(PLAN), selected_rows=plan['selected_rows'], candidate_rows=len(accepted),
        candidates=accepted, statuses=dict(statuses), results=results, ledger_sha256=ledger_pins,
        source_sha256=plan['source_sha256']))


if __name__ == '__main__':
    main()
