"""Freeze a reproducible checkpoint of completed repeated-word search ranges.

This aggregates search artifacts, not kernel proofs. Unprocessed rows remain in
the global residual. Existing reports, sources, and progress files are read only.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path

from check_closure_wave import FIELDS, load_input, machine_hash
from pipeline_sweep import digest, encoded, read_rows

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def fixed(path, content, check):
    if path.exists():
        if path.read_text() != content:
            raise ValueError(f'Frozen output differs: {path}')
    elif check:
        raise ValueError(f'Missing frozen output: {path}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def relative(path):
    return str(path.resolve().relative_to(REPO))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index', type=Path, default=ROOT/'build/wave3/repwl-stream/index.json')
    parser.add_argument('--weighted-input', type=Path, default=ROOT/'build/weighted-v2/full-cohort.txt')
    parser.add_argument('--prior-remaining', type=Path, default=ROOT/'build/wave3/timeout-retry/not-accepted.txt')
    parser.add_argument('--prior-report', type=Path, default=ROOT/'research/wave3-timeout-full.json')
    parser.add_argument('--batches', type=int, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.batches < 1:
        parser.error('--batches must be positive')
    descriptors = json.loads(args.index.read_text())['completed'][:args.batches]
    if len(descriptors) != args.batches:
        raise ValueError('Requested ranges have not all completed')
    weighted_rows = read_rows(args.weighted_input)
    prior_rows = read_rows(args.prior_remaining)
    prior = set(prior_rows)
    prior_report = json.loads(args.prior_report.read_text())
    if (len(prior) != prior_report['not_accepted_rows'] or
            digest(args.prior_remaining) != prior_report['not_accepted_sha256']):
        raise ValueError('Prior residual differs from its frozen report')
    if not prior <= set(weighted_rows):
        raise ValueError('Prior residual is not contained in the weighted cohort')
    source_path = ROOT/'research/repwl-stream/sources.json'
    source_hash = digest(source_path)
    rows, searched, rejected, timed_out, weighted_removed = [], set(), set(), set(), set()
    references = []
    end = 0
    wall_seconds = cpu_seconds = 0.
    for batch, descriptor in enumerate(descriptors):
        if descriptor['batch'] != batch or descriptor['input_range'][0] != end:
            raise ValueError('Completed ranges are not a contiguous prefix')
        report_path = REPO/descriptor['report']
        if digest(report_path) != descriptor['report_sha256']:
            raise ValueError('Range report changed')
        report = json.loads(report_path.read_text())
        manifest = report['manifest']
        start, end = descriptor['input_range']
        if (manifest['input_range'] != [start, end] or
                not 0 <= start < end <= len(weighted_rows) or
                report['source_version_sha256'] != source_hash or
                manifest['prior_remaining_sha256'] != digest(args.prior_remaining) or
                manifest['prior_report_sha256'] != digest(args.prior_report)):
            raise ValueError('Range belongs to a different input or source version')
        registry = REPO/manifest['weighted_registry']
        if digest(registry) != manifest['weighted_registry_sha256']:
            raise ValueError('Weighted registry changed')
        registry_data = json.loads(registry.read_text())
        if (registry_data['source']['input_range'] != [start, end] or
                registry_data['source']['input_sha256'] != digest(args.weighted_input)):
            raise ValueError('Weighted registry describes a different input range')
        raw = args.index.parent/f'batch{batch:03d}'
        cohort = set(read_rows(raw/'input.txt'))
        tail = set(read_rows(raw/'not-accepted.txt'))
        timeouts = set(read_rows(raw/'timeouts.txt'))
        if (digest(raw/'input.txt') != manifest['input_sha256'] or
                digest(raw/'not-accepted.txt') != report['not_accepted_sha256'] or
                digest(raw/'timeouts.txt') != report['remaining_timeouts_sha256'] or
                digest(raw/'candidates.tsv') != report['candidate_tsv_sha256']):
            raise ValueError('Raw range artifact changed')
        domain = prior & set(weighted_rows[start:end])
        removed = domain-cohort
        if (not cohort <= domain or len(cohort) != descriptor['input_rows'] or
                len(domain) != manifest['prior_remaining_rows'] or
                len(removed) != manifest['weighted_overlap_removed_rows']):
            raise ValueError('Range cohort differs from its recorded exclusions')
        if descriptor['candidate_rows']:
            proof_path = REPO/descriptor['proof_input']
            if digest(proof_path) != descriptor['proof_input_sha256']:
                raise ValueError('Compact replay input changed')
            _, selected = load_input(proof_path)
        else:
            selected = []
        with (raw/'candidates.tsv').open() as stream:
            raw_candidates = [{key: row[key] if key in ('machine', 'mode') else int(row[key])
                               for key in FIELDS}
                              for row in csv.DictReader(stream, delimiter='\t')]
        if selected != raw_candidates:
            raise ValueError('Compact replay input differs from search candidates')
        accepted = {row['machine'] for row in selected}
        if (accepted & tail or accepted | tail != cohort or not timeouts <= tail or
                len(accepted) != descriptor['candidate_rows'] or
                len(tail) != descriptor['not_accepted_rows'] or
                len(timeouts) != descriptor['remaining_timeout_rows'] or
                searched & cohort):
            raise ValueError('Range partition or counts differ')
        rows.extend(selected)
        searched |= cohort
        rejected |= tail
        timed_out |= timeouts
        weighted_removed |= removed
        wall_seconds += report['sum_row_seconds']
        cpu_seconds += report['sum_cpu_seconds']
        references.append(descriptor)
    rows.sort(key=machine_hash)
    accepted = {row['machine'] for row in rows}
    if len(accepted) != len(rows):
        raise ValueError('Duplicate candidate between ranges')
    global_tail = prior-weighted_removed-accepted
    order = lambda names: sorted(names, key=lambda name: hashlib.sha256(name.encode()).digest())
    text = io.StringIO()
    writer = csv.DictWriter(text, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    outputs = {'candidates.tsv': text.getvalue(),
               'searched-not-accepted.txt': encoded(order(rejected)),
               'remaining-timeouts.txt': encoded(order(timed_out)),
               'global-residual-after-prefix.txt': encoded(order(global_tail))}
    for name, content in outputs.items():
        fixed(args.output_dir/name, content, args.check)
    result = {
        'status': 'Frozen completed-range search checkpoint; all candidates require independent kernel replay.',
        'source_range': [0, end], 'source_total_rows': len(weighted_rows),
        'complete_source_cohort': end == len(weighted_rows), 'completed_ranges': len(descriptors),
        'prior_remaining_rows': len(prior), 'searched_rows': len(searched),
        'weighted_candidate_exclusions_in_prefix': len(weighted_removed),
        'candidate_rows': len(rows), 'searched_not_accepted_rows': len(rejected),
        'candidate_tsv_sha256': hashlib.sha256(outputs['candidates.tsv'].encode()).hexdigest(),
        'remaining_timeout_rows': len(timed_out), 'global_residual_after_prefix_rows': len(global_tail),
        'unprocessed_prior_rows': len(prior-set(weighted_rows[:end])),
        'sum_row_seconds': round(wall_seconds, 6), 'sum_cpu_seconds': round(cpu_seconds, 6),
        'kernel_checked_rows': 0, 'census_linked_rows': 0,
        'sources_sha256': {relative(Path(__file__)): digest(Path(__file__)),
                           'four/tools/check_closure_wave.py': digest(ROOT/'tools/check_closure_wave.py'),
                           'four/tools/pipeline_sweep.py': digest(ROOT/'tools/pipeline_sweep.py'),
                           relative(source_path): source_hash,
                           relative(args.weighted_input): digest(args.weighted_input),
                           relative(args.prior_remaining): digest(args.prior_remaining),
                           relative(args.prior_report): digest(args.prior_report)},
        'ranges': references,
        'output_directory': relative(args.output_dir),
        'outputs_sha256': {name: hashlib.sha256(content.encode()).hexdigest()
                           for name, content in outputs.items()},
    }
    fixed(args.report, json.dumps(result, indent=2, sort_keys=True)+'\n', args.check)
    print(json.dumps({key: result[key] for key in ('completed_ranges', 'source_range', 'searched_rows',
          'candidate_rows', 'remaining_timeout_rows', 'global_residual_after_prefix_rows')}, sort_keys=True))


if __name__ == '__main__':
    main()
