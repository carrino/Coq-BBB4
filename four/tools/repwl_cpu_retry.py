"""Retry completed repeated-word liveness timeouts with a process-CPU budget.

The cohort is a frozen stream checkpoint. One previously timed-out width is
chosen per machine, preferring the smaller closed graph. Results remain search
candidates until the ordinary, uncut Coq checker is independently replayed.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess

from pipeline_sweep import digest, encoded, read_rows
from repwl_diagnostics import result_rows
from check_closure_wave import FIELDS, machine_hash

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def fixed(path, content, check=False):
    if path.exists():
        if path.read_text() != content:
            raise ValueError(f'Frozen artifact differs: {path}')
    elif check:
        raise ValueError(f'Missing artifact: {path}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def json_text(data):
    return json.dumps(data, indent=2, sort_keys=True)+'\n'


def relative(path):
    return str(path.resolve().relative_to(REPO))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, required=True)
    parser.add_argument('--sample', type=int, default=64)
    parser.add_argument('--cpu-timeout', type=float, default=2.)
    parser.add_argument('--probe', type=Path, default=ROOT/'build/wave3/repwl-cpu/probe')
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.sample < 0 or not 0 < args.cpu_timeout < float('inf'):
        parser.error('Invalid sample size or CPU timeout')
    checkpoint = json.loads(args.checkpoint.read_text())
    prior_candidates = REPO/checkpoint['output_directory']/'candidates.tsv'
    if digest(prior_candidates) != checkpoint['candidate_tsv_sha256']:
        raise ValueError('Checkpoint candidate inventory changed')
    with prior_candidates.open() as source:
        accepted = {row['machine'] for row in csv.DictReader(source, delimiter='\t')}
    choices, sources = {}, []
    for descriptor in checkpoint['ranges']:
        report_path = REPO/descriptor['report']
        if digest(report_path) != descriptor['report_sha256']:
            raise ValueError('Stream range report changed')
        report = json.loads(report_path.read_text())
        batch = descriptor['batch']
        if report['manifest']['bound'] != 4096:
            raise ValueError('Unexpected source bound')
        for stage in report['results']:
            width = stage['width']
            expected_parameters = {'size': width, 'extra': 2, 'anchor': 0, 'fuel': 5120,
                                   'size_cap': 32, 'mirror': False, 'swap23': False}
            if width not in (2, 3) or any(stage['result'][key] != value
                                         for key, value in expected_parameters.items()):
                raise ValueError('Unexpected source checker parameters')
            stage_report = REPO/stage['report']
            if digest(stage_report) != stage['report_sha256']:
                raise ValueError('Stage report changed')
            directory = (ROOT/'build/wave3/repwl-prefix000'/f'width{width}' if batch == 0
                         else ROOT/'build/wave3/repwl-stream'/f'batch{batch:03d}'/f'width{width}')
            log = directory/'stage-00.tsv'
            if digest(log) != stage['result']['log_sha256']:
                raise ValueError('Stage diagnostic log changed')
            expected = read_rows(directory/'selected.txt')
            results = result_rows(log, expected)
            if len(results) != len(expected):
                raise ValueError('Incomplete source stage')
            sources.append({'batch': batch, 'width': width, 'report': relative(report_path),
                            'report_sha256': digest(report_path), 'stage_report': relative(stage_report),
                            'stage_report_sha256': digest(stage_report),
                            'log': relative(log), 'log_sha256': digest(log)})
            for row in results:
                machine = row['machine']
                if (machine in accepted or row['status'] != 'timeout' or
                        row['phase'] != 'liveness'):
                    continue
                if row['nodes'] <= 0:
                    raise ValueError('Liveness timeout has no recorded closed graph')
                choice = {'machine': machine, 'width': width, 'source_batch': batch,
                          'previous_nodes': row['nodes'], 'previous_cpu_seconds': row['cpu_seconds'],
                          'previous_wall_seconds': row['seconds']}
                key = lambda value: (value['previous_nodes'], value['width'])
                if machine not in choices or key(choice) < key(choices[machine]):
                    choices[machine] = choice
    selected = sorted(choices.values(), key=lambda row: hashlib.sha256(row['machine'].encode()).digest())
    if args.sample:
        selected = selected[:args.sample]
    if not selected:
        raise ValueError('No eligible liveness timeouts')
    parameters = {'bound': 4096, 'threshold': 2, 'anchor': 0, 'fuel': 5120, 'size_cut': 32}
    pinned = [Path(__file__), ROOT/'tools/diagnose_repwl_cpu.ml',
              ROOT/'tools/repwl_diagnostics.py', ROOT/'tools/pipeline_sweep.py',
              ROOT/'tools/check_closure_wave.py', ROOT/'build/advanced/checkers.ml',
              ROOT/'research/repwl-stream/sources.json', args.probe]
    manifest = {
        'status': 'Search retry input, not a proof inventory.',
        'checkpoint': relative(args.checkpoint), 'checkpoint_sha256': digest(args.checkpoint),
        'eligible_rows': len(choices), 'selected_rows': len(selected),
        'selection': 'Lowest SHA256(machine), one timed-out width per machine; prefer fewer closed nodes, then smaller width.',
        'timeout_clock': 'process CPU (user plus system), Unix.ITIMER_PROF',
        'timeout_cpu_seconds_per_row': args.cpu_timeout,
        'parameters': parameters, 'selected': selected, 'sources': sources,
        'sources_sha256': {relative(path): digest(path) for path in pinned},
    }
    fixed(args.output_dir/'manifest.json', json_text(manifest), args.check)
    candidates, summaries, unresolved = [], [], []
    for width in (2, 3):
        group = [row['machine'] for row in selected if row['width'] == width]
        if not group:
            continue
        input_path = args.output_dir/f'width{width}.txt'
        fixed(input_path, encoded(group), args.check)
        log = args.output_dir/f'width{width}.tsv'
        results = result_rows(log, group, repair=not args.check)
        todo = group[len(results):]
        if todo:
            if args.check:
                raise ValueError('Incomplete retry group')
            todo_path = args.output_dir/f'width{width}-todo.txt'
            todo_path.write_text(encoded(todo))
            command = [str(args.probe.resolve()), '4096', str(width), '2', '0', '5120', '32',
                       str(args.cpu_timeout), str(todo_path.resolve())]
            with log.open('a') as stream:
                subprocess.run(command, stdout=stream, check=True)
            results = result_rows(log, group)
        if len(results) != len(group):
            raise ValueError('Incomplete retry group')
        for row in results:
            if row['status'] == 'candidate':
                candidates.append({'machine': row['machine'], 'mode': 'rw', 'bound': 4096,
                                   'size': width, 'anchor': 0, 'fuel': 5120, 'extra': 2, 'history': 0})
            else:
                unresolved.append(row['machine'])
        summaries.append({'width': width, 'rows': len(group),
                          'statuses': dict(sorted(Counter(row['status'] for row in results).items())),
                          'failure_phases': dict(sorted(Counter(row['phase'] for row in results
                                                               if row['status'] != 'candidate').items())),
                          'sum_wall_seconds': round(sum(row['seconds'] for row in results), 6),
                          'sum_cpu_seconds': round(sum(row['cpu_seconds'] for row in results), 6),
                          'log_sha256': digest(log)})
        print(json.dumps(summaries[-1], sort_keys=True), flush=True)
    candidates.sort(key=machine_hash)
    unresolved.sort(key=lambda name: hashlib.sha256(name.encode()).digest())
    table = io.StringIO()
    writer = csv.DictWriter(table, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(candidates)
    fixed(args.output_dir/'candidates.tsv', table.getvalue(), args.check)
    fixed(args.output_dir/'not-accepted.txt', encoded(unresolved), args.check)
    report = {'status': 'Completed process-CPU-budgeted RW search retry; ordinary uncut kernel replay is still required.',
              'manifest': manifest, 'results': summaries, 'candidate_rows': len(candidates),
              'not_accepted_rows': len(unresolved),
              'candidate_tsv_sha256': digest(args.output_dir/'candidates.tsv'),
              'not_accepted_sha256': digest(args.output_dir/'not-accepted.txt'),
              'kernel_checked_rows': 0, 'census_linked_rows': 0}
    fixed(args.report, json_text(report), args.check)
    print(f'{len(candidates)} candidates; {len(unresolved)} unresolved; no proof claims.', flush=True)


if __name__ == '__main__':
    main()
