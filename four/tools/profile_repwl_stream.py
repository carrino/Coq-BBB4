"""Describe retained search outcomes from a frozen RW stream checkpoint.

The resulting ledger describes research failures and timeouts, never a proof
that a machine is undecidable or outside the claimed mathematical bound.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path

from pipeline_sweep import digest, read_rows
from repwl_diagnostics import result_rows

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
COLUMNS = [('status', 'status'), ('phase', 'phase'), ('closed_nodes', 'nodes'),
           ('expanded_nodes', 'expanded_nodes'), ('max_node_size', 'max_node_size'),
           ('cpu_seconds', 'cpu_seconds')]


def fixed(path, content, check):
    if path.exists():
        if path.read_text() != content:
            raise ValueError(f'Frozen artifact differs: {path}')
    elif check:
        raise ValueError(f'Missing artifact: {path}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    checkpoint = json.loads(args.checkpoint.read_text())
    residual_path = REPO/checkpoint['output_directory']/'searched-not-accepted.txt'
    if digest(residual_path) != checkpoint['outputs_sha256']['searched-not-accepted.txt']:
        raise ValueError('Checkpoint residual changed')
    residual = set(residual_path.read_text().splitlines())
    records = {2: {}, 3: {}}
    counts = {2: Counter(), 3: Counter()}
    sources = []
    for descriptor in checkpoint['ranges']:
        report_path = REPO/descriptor['report']
        if digest(report_path) != descriptor['report_sha256']:
            raise ValueError('Range report changed')
        report = json.loads(report_path.read_text())
        batch = descriptor['batch']
        for stage in report['results']:
            width = stage['width']
            if width not in records:
                raise ValueError('Unexpected RW width')
            directory = (ROOT/'build/wave3/repwl-prefix000'/f'width{width}' if batch == 0
                         else ROOT/'build/wave3/repwl-stream'/f'batch{batch:03d}'/f'width{width}')
            log = directory/'stage-00.tsv'
            if digest(log) != stage['result']['log_sha256']:
                raise ValueError('Diagnostic log changed')
            expected = read_rows(directory/'selected.txt')
            rows = result_rows(log, expected)
            if len(rows) != len(expected):
                raise ValueError('Incomplete diagnostic log')
            count = Counter(row['status'] for row in rows)
            if dict(count) != stage['result']['statuses']:
                raise ValueError('Stage status counts differ')
            counts[width].update(count)
            for row in rows:
                if row['machine'] in records[width]:
                    raise ValueError('Duplicate machine between ranges')
                records[width][row['machine']] = row
            sources.append({'batch': batch, 'width': width,
                            'report': descriptor['report'], 'report_sha256': digest(report_path),
                            'log': str(log.relative_to(REPO)), 'log_sha256': digest(log)})
    if not residual <= set(records[2]) & set(records[3]):
        raise ValueError('Retained machine is missing a stage outcome')
    fields = ['machine'] + [f'width{width}_{name}' for width in (3, 2) for name, _ in COLUMNS]
    table = io.StringIO()
    writer = csv.DictWriter(table, fields, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    pairs, timeout_phases = Counter(), Counter()
    timeouts = set()
    for machine in sorted(residual, key=lambda name: hashlib.sha256(name.encode()).digest()):
        row = {'machine': machine}
        pair, phases = [], set()
        for width in (3, 2):
            source = records[width][machine]
            if source['status'] == 'candidate':
                raise ValueError('Candidate remains in the checkpoint residual')
            pair.append(source['status'])
            row.update({f'width{width}_{name}': source[key] for name, key in COLUMNS})
            if source['status'] == 'timeout':
                timeouts.add(machine)
                phases.add(source['phase'])
        pairs[tuple(pair)] += 1
        timeout_phases.update(phases)
        writer.writerow(row)
    if len(timeouts) != checkpoint['remaining_timeout_rows']:
        raise ValueError('Retained timeout count differs from checkpoint')
    ledger = args.output_dir/'failure-profile.tsv'
    fixed(ledger, table.getvalue(), args.check)
    report = {
        'status': 'Research outcome profile only; retained rows are unresolved, not mathematical counterexamples.',
        'checkpoint': str(args.checkpoint.resolve().relative_to(REPO)),
        'checkpoint_sha256': digest(args.checkpoint),
        'source_range': checkpoint['source_range'],
        'complete_source_cohort': checkpoint['complete_source_cohort'],
        'searched_rows': checkpoint['searched_rows'], 'candidate_rows': checkpoint['candidate_rows'],
        'retained_rows': len(residual), 'retained_timeout_rows': len(timeouts),
        'retained_timeout_phases': dict(sorted(timeout_phases.items())),
        'counter_meanings': {'closed_nodes': 'Size after closure succeeds; zero if closure never completed.',
                             'expanded_nodes': 'Calls made by the closure search to its successor function.'},
        'all_stage_status_counts': {str(width): dict(sorted(counts[width].items())) for width in (3, 2)},
        'retained_status_pairs': [{'width3': pair[0], 'width2': pair[1], 'rows': count}
                                  for pair, count in sorted(pairs.items(), key=lambda item: (-item[1], item[0]))],
        'ledger': str(ledger.resolve().relative_to(REPO)), 'ledger_sha256': digest(ledger),
        'sources': sources,
        'source_sha256': {str(path.relative_to(ROOT)): digest(path) for path in
                          (Path(__file__), ROOT/'tools/pipeline_sweep.py', ROOT/'tools/repwl_diagnostics.py')},
    }
    fixed(args.report, json.dumps(report, indent=2, sort_keys=True)+'\n', args.check)
    print(json.dumps({key: report[key] for key in
                      ('retained_rows', 'retained_timeout_rows', 'retained_timeout_phases',
                       'all_stage_status_counts')}, sort_keys=True))


if __name__ == '__main__':
    main()
