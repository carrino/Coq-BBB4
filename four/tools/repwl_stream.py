"""Follow immutable weighted-search ranges with two repeated-word rungs.

Only completed weighted misses in the frozen prior remainder are searched.
Every completed range receives an immutable report and compact ordinary Coq
replay input. The size cut is a search screen; the replay input uses rw_check
without that cut. No search result is counted as a kernel proof.
"""
import argparse
import base64
import csv
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import subprocess
import time
import zlib

from pipeline_sweep import digest, encoded, read_rows
from weighted_codec_v2 import bundle_decode

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
FIELDS = ('machine', 'stage', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history')
PROOF_FIELDS = ('machine', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history')
CHECK_ONLY = False


def frozen(path, content):
    if path.exists():
        if path.read_text() != content:
            raise ValueError(f'Frozen artifact differs: {path}')
    else:
        if CHECK_ONLY:
            raise ValueError(f'Missing frozen artifact: {path}')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def json_text(value):
    return json.dumps(value, indent=2, sort_keys=True)+'\n'


def relative(path):
    return str(path.resolve().relative_to(REPO))


def process_snapshot(args, snapshot, weighted_rows, remaining):
    batch = snapshot['batch']
    name = f'batch{batch:03d}'
    directory = args.output_dir/name
    if not CHECK_ONLY:
        directory.mkdir(parents=True, exist_ok=True)
    registry_path = Path(snapshot['registry'])
    if digest(registry_path) != snapshot['registry_sha256']:
        raise ValueError('Weighted snapshot registry changed')
    registry = json.loads(registry_path.read_text())
    start, end = registry['source']['input_range']
    if [start, end] != snapshot['input_range'] or not 0 <= start < end <= len(weighted_rows):
        raise ValueError('Invalid snapshot range')
    if registry['source']['input_sha256'] != digest(args.weighted_input):
        raise ValueError('Snapshot belongs to a different weighted input')
    domain = set(weighted_rows[start:end])
    weighted = set()
    for bundle in registry['bundles']:
        path = ROOT/bundle['path']
        if digest(path) != bundle['sha256']:
            raise ValueError('Weighted certificate bundle changed')
        rows = bundle_decode(path.read_text())
        if len(rows) != bundle['rows']:
            raise ValueError('Weighted certificate bundle row count differs')
        for row in rows:
            machine = row['machine']
            if machine not in domain or machine in weighted:
                raise ValueError('Duplicate or out-of-range weighted candidate')
            weighted.add(machine)
    if len(weighted) != snapshot['candidate_rows']:
        raise ValueError('Snapshot candidate count differs')
    prior = domain & remaining
    cohort = sorted(prior-weighted, key=lambda m: hashlib.sha256(m.encode()).digest())
    input_path = directory/'input.txt'
    frozen(input_path, encoded(cohort))
    manifest = {
        'status': 'Completed-domain search input; weighted candidates remain untrusted.',
        'batch': batch, 'input_range': [start, end], 'weighted_rows': end-start,
        'prior_remaining_rows': len(prior), 'weighted_candidate_rows': len(weighted),
        'weighted_overlap_removed_rows': len(prior & weighted),
        'input_rows': len(cohort), 'input_sha256': digest(input_path),
        'weighted_registry': relative(registry_path), 'weighted_registry_sha256': digest(registry_path),
        'prior_remaining_sha256': digest(args.remaining),
        'prior_report_sha256': digest(args.prior_report),
        'widths': [3, 2], 'bound': 4096, 'anchor': 0, 'fuel': 5120,
        'threshold': 2, 'size_cut': 32, 'timeout_seconds_per_row': args.timeout,
        'stream_source_sha256': digest(Path(__file__)),
        'weighted_codec_sha256': digest(ROOT/'tools/weighted_codec_v2.py'),
    }
    frozen(directory/'manifest.json', json_text(manifest))
    reports = []
    candidates = []
    unresolved_timeouts = set()
    current_input = input_path
    for index, width in enumerate([3, 2]):
        if not current_input.read_text():
            break
        stage = {'size': width, 'extra': 2, 'anchor': 0, 'fuel': 5120,
                 'size_cap': 32, 'mirror': False, 'swap23': False}
        # Adopt the already completed initial range without rerunning search.
        if batch == 0 and args.adopt_first:
            stage_dir = ROOT/f'build/wave3/repwl-prefix000/width{width}'
            stage_report = ROOT/f'research/wave3-repwl-prefix000-width{width}.json'
        else:
            stage_dir = directory/f'width{width}'
            stage_report = directory/f'width{width}.json'
        preset = directory/f'width{width}-stages.json'
        frozen(preset, json_text([stage]))
        command = ['python3', str(ROOT/'tools/repwl_diagnostics.py'),
                   '--input', str(current_input), '--stages', str(preset),
                   '--output-dir', str(stage_dir), '--report', str(stage_report),
                   '--sample', '0', '--timeout', str(args.timeout)]
        if args.check or (batch == 0 and args.adopt_first):
            command.append('--check')
        subprocess.run(command, cwd=REPO, check=True, stdout=subprocess.DEVNULL)
        report = json.loads(stage_report.read_text())
        reports.append({'width': width, 'report': relative(stage_report),
                        'report_sha256': digest(stage_report), 'result': report['results'][0],
                        'candidate_rows': report['candidate_rows']})
        source_version = {key: report['manifest'][key] for key in
                          ('probe_sha256', 'extraction_sha256', 'sources_sha256')}
        source_version['stream_source_sha256'] = digest(Path(__file__))
        source_version['weighted_codec_sha256'] = digest(ROOT/'tools/weighted_codec_v2.py')
        frozen(args.research_dir/'sources.json', json_text(source_version))
        with (stage_dir/'candidates.tsv').open() as source:
            for raw in csv.DictReader(source, delimiter='\t'):
                if raw['machine'] != raw['tested_machine'] or raw['mirror'] != 'false' or raw['swap23'] != 'false':
                    raise ValueError('Unexpected symmetry requires a different replay adapter')
                candidates.append({'machine': raw['machine'], 'stage': index, 'mode': 'rw',
                                   'bound': 4096, 'size': width, 'anchor': 0,
                                   'fuel': 5120, 'extra': 2, 'history': 0})
        with (stage_dir/'stage-00.tsv').open() as source:
            for raw in csv.DictReader(source, delimiter='\t'):
                if raw['status'] == 'timeout':
                    unresolved_timeouts.add(raw['machine'])
        current_input = stage_dir/'not-accepted.txt'
    candidates.sort(key=lambda row: hashlib.sha256(row['machine'].encode()).digest())
    accepted = {row['machine'] for row in candidates}
    if len(accepted) != len(candidates) or not accepted <= set(cohort):
        raise ValueError('Duplicate or out-of-scope RW candidate')
    tail = [machine for machine in cohort if machine not in accepted]
    unresolved_timeouts &= set(tail)
    text = io.StringIO()
    writer = csv.DictWriter(text, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader(); writer.writerows(candidates)
    frozen(directory/'candidates.tsv', text.getvalue())
    frozen(directory/'not-accepted.txt', encoded(tail))
    frozen(directory/'timeouts.txt', encoded(sorted(unresolved_timeouts)))
    report_path = args.research_dir/f'{name}.json'
    summary = {
        'status': 'Complete RW search on one frozen weighted residual range; no new kernel claims.',
        'manifest': manifest, 'source_version_sha256': digest(args.research_dir/'sources.json'),
        'results': reports, 'candidate_rows': len(candidates), 'not_accepted_rows': len(tail),
        'remaining_timeout_rows': len(unresolved_timeouts),
        'candidate_tsv_sha256': digest(directory/'candidates.tsv'),
        'not_accepted_sha256': digest(directory/'not-accepted.txt'),
        'remaining_timeouts_sha256': digest(directory/'timeouts.txt'),
        'sum_row_seconds': round(sum(r['result']['sum_row_seconds'] for r in reports), 6),
        'sum_cpu_seconds': round(sum(r['result']['sum_cpu_seconds'] for r in reports), 6),
        'kernel_checked_rows': 0, 'census_linked_rows': 0,
    }
    frozen(report_path, json_text(summary))
    proof_path = args.research_dir/f'{name}-proof-input.json'
    if candidates:
        data = {'selection': 'All candidates from one disjoint completed weighted residual range. Ordinary uncut RW checker replay is required.',
                'search_sources': [{'report': relative(report_path), 'report_sha256': digest(report_path),
                                    'candidate_tsv_sha256': digest(directory/'candidates.tsv'),
                                    'candidate_rows': len(candidates)}],
                'excluded_ledgers_sha256': {}, 'columns': list(PROOF_FIELDS),
                'selected_rows': len(candidates),
                'rows': [[row[key] for key in PROOF_FIELDS] for row in candidates]}
        payload = json.dumps(data, separators=(',', ':'), sort_keys=True).encode()
        frozen(proof_path, json_text({'encoding': 'zlib-base64',
                                      'uncompressed_sha256': hashlib.sha256(payload).hexdigest(),
                                      'data': base64.b64encode(zlib.compress(payload, 9)).decode()}))
    descriptor = {'batch': batch, 'input_range': [start, end], 'input_rows': len(cohort),
                  'candidate_rows': len(candidates), 'not_accepted_rows': len(tail),
                  'remaining_timeout_rows': len(unresolved_timeouts),
                  'report': relative(report_path), 'report_sha256': digest(report_path),
                  'proof_input': relative(proof_path) if candidates else None,
                  'proof_input_sha256': digest(proof_path) if candidates else None}
    print(json.dumps(descriptor, sort_keys=True), flush=True)
    return descriptor


def main():
    global CHECK_ONLY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index', type=Path, default=ROOT/'build/weighted-v2/full-snapshots-index.json')
    parser.add_argument('--weighted-input', type=Path, default=ROOT/'build/weighted-v2/full-cohort.txt')
    parser.add_argument('--remaining', type=Path, default=ROOT/'build/wave3/timeout-retry/not-accepted.txt')
    parser.add_argument('--prior-report', type=Path, default=ROOT/'research/wave3-timeout-full.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/wave3/repwl-stream')
    parser.add_argument('--research-dir', type=Path, default=ROOT/'research/repwl-stream')
    parser.add_argument('--timeout', type=float, default=1.)
    parser.add_argument('--max-batches', type=int, default=0)
    parser.add_argument('--adopt-first', action='store_true')
    parser.add_argument('--watch', action='store_true')
    parser.add_argument('--stop-utc', help='Stop before starting another range after this ISO UTC time')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    CHECK_ONLY = args.check
    if not 0 < args.timeout < float('inf') or args.max_batches < 0 or (args.check and args.watch):
        parser.error('Invalid timeout, batch limit, or watch/check combination')
    for key in ('index', 'weighted_input', 'remaining', 'prior_report', 'output_dir', 'research_dir'):
        setattr(args, key, getattr(args, key).resolve())
    stop = datetime.fromisoformat(args.stop_utc) if args.stop_utc else None
    if stop and stop.tzinfo is None:
        parser.error('--stop-utc must include a UTC offset')
    weighted_rows = read_rows(args.weighted_input)
    remaining = set(read_rows(args.remaining))
    prior = json.loads(args.prior_report.read_text())
    if prior['not_accepted_rows'] != len(remaining) or prior['not_accepted_sha256'] != digest(args.remaining):
        raise ValueError('Prior remainder differs from its report')
    seen = {}
    while True:
        if stop and datetime.now(timezone.utc) >= stop:
            break
        try:
            index = json.loads(args.index.read_text())
        except json.JSONDecodeError:
            if not args.watch:
                raise
            time.sleep(1)
            continue
        snapshots = index['snapshots']
        if len({snapshot['batch'] for snapshot in snapshots}) != len(snapshots):
            raise ValueError('Duplicate snapshot batch identifiers')
        previous = 0
        for snapshot in snapshots:
            if snapshot['input_range'][0] != previous:
                raise ValueError('Snapshot ranges overlap or have a gap')
            previous = snapshot['input_range'][1]
        progressed = False
        for snapshot in snapshots:
            batch = snapshot['batch']
            if batch in seen:
                continue
            if args.max_batches and len(seen) >= args.max_batches:
                return
            if stop and datetime.now(timezone.utc) >= stop:
                return
            descriptor = process_snapshot(args, snapshot, weighted_rows, remaining)
            seen[batch] = descriptor
            progress = {'status': 'Mutable progress index of immutable completed RW ranges; no proof claims.',
                        'completed': [seen[key] for key in sorted(seen)],
                        'candidate_rows': sum(row['candidate_rows'] for row in seen.values()),
                        'input_rows': sum(row['input_rows'] for row in seen.values())}
            if not args.check:
                args.output_dir.mkdir(parents=True, exist_ok=True)
                (args.output_dir/'index.json').write_text(json_text(progress))
            progressed = True
        if not args.watch or previous == len(weighted_rows):
            break
        if not progressed:
            time.sleep(10)


if __name__ == '__main__':
    main()
