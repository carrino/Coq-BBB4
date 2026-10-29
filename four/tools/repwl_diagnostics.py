"""Measure repeated-word failure phases and optional size cuts on a frozen cohort.

Every stage tests the same deterministically selected rows. A size cut only
retains an unresolved row. Candidates must replay the ordinary, uncut Coq
checker, with the recorded symmetry transported back to the original machine.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess

from advanced_sweep import source_hashes
from group_families import parse, render, rename
from pipeline_sweep import digest, encoded, read_rows

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROBE = ROOT/'build/wave3/diagnostic/rw-probe'
LOG_FIELDS = ('machine', 'status', 'phase', 'nodes', 'expanded_nodes',
              'max_node_size', 'seconds', 'cpu_seconds')
STATUSES = {'candidate', 'boot_halt', 'node_cut', 'blocked', 'fuel_exhausted',
            'closure_failure', 'membership_failure', 'prefix_failure',
            'ranking_failure', 'timeout', 'stack_overflow'}
CERT_FIELDS = ('machine', 'tested_machine', 'stage', 'mirror', 'swap23',
               'bound', 'size', 'anchor', 'fuel', 'extra', 'size_cap')


def transform(machine, stage):
    perm = (0, 1, 3, 2) if stage['swap23'] else (0, 1, 2, 3)
    return render(rename(parse(machine), perm, mirror=stage['mirror'], swap=False))


def result_rows(path, expected, repair=False):
    if not path.exists():
        return []
    raw = path.read_bytes()
    if raw and not raw.endswith(b'\n'):
        if not repair:
            raise ValueError(f'Incomplete log line: {path}')
        raw = raw[:raw.rfind(b'\n')+1]
        path.write_bytes(raw)
    if not raw:
        return []
    reader = csv.DictReader(io.StringIO(raw.decode()), delimiter='\t')
    if tuple(reader.fieldnames or ()) != LOG_FIELDS:
        raise ValueError(f'Unexpected diagnostic log columns: {path}')
    rows = []
    for row in reader:
        # Resumed native processes each emit a header. Keep only result rows.
        if tuple(row.values()) == LOG_FIELDS:
            continue
        index = len(rows)
        if index >= len(expected) or row['machine'] != expected[index]:
            raise ValueError(f'Unexpected row identity/order in {path}: {index}')
        if row['status'] not in STATUSES:
            raise ValueError(f'Unexpected result status: {row["status"]}')
        for field in ('nodes', 'expanded_nodes', 'max_node_size'):
            row[field] = int(row[field])
            if row[field] < 0:
                raise ValueError('Negative diagnostic counter')
        for field in ('seconds', 'cpu_seconds'):
            row[field] = float(row[field])
            if not 0 <= row[field] < float('inf'):
                raise ValueError('Invalid diagnostic timing')
        rows.append(row)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--stages', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--probe', type=Path, default=DEFAULT_PROBE)
    parser.add_argument('--sample', type=int, default=64)
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--timeout', type=float, default=1.)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.sample < 0 or args.bound < 0 or not 0 < args.timeout < float('inf'):
        parser.error('Invalid bound, sample, or timeout')
    stages = json.loads(args.stages.read_text())
    if not stages:
        parser.error('At least one stage is required')
    for stage in stages:
        if set(stage) != {'size', 'extra', 'anchor', 'fuel', 'size_cap', 'mirror', 'swap23'}:
            parser.error('Unexpected stage fields')
        if any(type(stage[k]) is not int for k in ('size', 'extra', 'anchor', 'fuel', 'size_cap')):
            parser.error('Numeric parameters must be integers')
        if any(type(stage[k]) is not bool for k in ('mirror', 'swap23')):
            parser.error('Symmetry flags must be booleans')
        if stage['size'] < 1 or stage['extra'] < 2 or stage['fuel'] < 1 or stage['size_cap'] < 0:
            parser.error('Invalid checker parameter')
        if not 0 <= stage['anchor'] <= args.bound:
            parser.error('Anchor must be at most the recorded bound')
    inventory = read_rows(args.input)
    selected = sorted(inventory, key=lambda m: hashlib.sha256(m.encode()).digest())
    if args.sample:
        selected = selected[:args.sample]
    manifest = {
        'input_rows': len(inventory), 'input_sha256': digest(args.input),
        'selected_rows': len(selected),
        'selected_sha256': hashlib.sha256(encoded(selected).encode()).hexdigest(),
        'selection': 'lowest SHA256(machine UTF-8) values' if args.sample else 'all rows ordered by SHA256(machine UTF-8)',
        'bound': args.bound, 'both_bounds': True, 'stages': stages,
        'timeout_seconds_per_row': args.timeout,
        'probe_sha256': digest(args.probe),
        'extraction_sha256': digest(ROOT/'build/advanced/checkers.ml'),
        'sources_sha256': {**source_hashes(), **{
            str(p.relative_to(ROOT)): digest(p) for p in
            (Path(__file__), ROOT/'tools/diagnose_repwl.ml', ROOT/'tools/group_families.py')}}}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = args.output_dir/'manifest.json'
    if manifest_path.exists():
        if json.loads(manifest_path.read_text()) != manifest:
            raise ValueError('Input, parameters, source, or binary differs; use a new output directory')
    elif args.check:
        raise ValueError('No saved manifest')
    else:
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
        (args.output_dir/'selected.txt').write_text(encoded(selected))
    if (args.output_dir/'selected.txt').read_text() != encoded(selected):
        raise ValueError('Selected input differs')
    summaries = []
    certificates = []
    found = set()
    for index, stage in enumerate(stages):
        tested = [transform(machine, stage) for machine in selected]
        path = args.output_dir/f'stage-{index:02d}.tsv'
        results = result_rows(path, tested, repair=not args.check)
        todo = tested[len(results):]
        if todo:
            if args.check:
                raise ValueError(f'Stage {index} is incomplete')
            todo_path = args.output_dir/f'stage-{index:02d}-todo.txt'
            todo_path.write_text(encoded(todo))
            command = [str(args.probe.resolve()), str(args.bound), str(stage['size']),
                       str(stage['extra']), str(stage['anchor']), str(stage['fuel']),
                       str(stage['size_cap']), str(args.timeout), str(todo_path.resolve())]
            with path.open('a') as output:
                subprocess.run(command, stdout=output, check=True)
            results = result_rows(path, tested)
        if len(results) != len(selected):
            raise ValueError(f'Incomplete stage {index}')
        winners = {machine for machine, row in zip(selected, results) if row['status'] == 'candidate'}
        summary = {'stage': index, **stage, 'rows': len(results),
                   'statuses': dict(sorted(Counter(row['status'] for row in results).items())),
                   'failure_phases': dict(sorted(Counter(row['phase'] for row in results
                                                        if row['status'] != 'candidate').items())),
                   'new_candidate_rows': len(winners-found),
                   'sum_row_seconds': round(sum(row['seconds'] for row in results), 6),
                   'sum_cpu_seconds': round(sum(row['cpu_seconds'] for row in results), 6),
                   'max_node_size': max((row['max_node_size'] for row in results), default=0),
                   'max_candidate_node_size': max((row['max_node_size'] for row in results
                                                  if row['status'] == 'candidate'), default=0),
                   'log_sha256': digest(path)}
        certificates.extend({'machine': machine, 'tested_machine': row['machine'],
                             'stage': index, 'bound': args.bound, **stage}
                            for machine, row in zip(selected, results)
                            if machine in winners-found)
        found |= winners
        summaries.append(summary)
        print(json.dumps(summary, sort_keys=True), flush=True)
    candidates = '\t'.join(CERT_FIELDS)+'\n'+''.join(
        '\t'.join(str(cert[field]).lower() if type(cert[field]) is bool else str(cert[field])
                  for field in CERT_FIELDS)+'\n' for cert in certificates)
    remaining = [machine for machine in selected if machine not in found]
    report = {'status': 'Untrusted diagnostic search; candidates require ordinary uncut checker replay and symmetry transport.',
              'manifest': manifest, 'results': summaries, 'candidate_rows': len(found),
              'not_accepted_rows': len(remaining),
              'candidate_tsv_sha256': hashlib.sha256(candidates.encode()).hexdigest(),
              'not_accepted_sha256': hashlib.sha256(encoded(remaining).encode()).hexdigest(),
              'kernel_checked_rows': 0, 'census_linked_rows': 0}
    for path, content in {
        args.output_dir/'candidates.tsv': candidates,
        args.output_dir/'not-accepted.txt': encoded(remaining),
        args.report: json.dumps(report, indent=2, sort_keys=True)+'\n',
    }.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise ValueError(f'Generated output differs: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(f'{len(found)} distinct candidates; {len(remaining)} not accepted; no proof claims.', flush=True)


if __name__ == '__main__':
    main()
