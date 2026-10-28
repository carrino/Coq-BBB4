"""Select only surviving per-stage timeouts from complete frozen search runs.

The supplied cohort may already exclude candidates from other methods. Each
output is a search-work queue, never a claim that its rows are undecidable.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path

from pipeline_sweep import digest, encoded, read_results, read_rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cohort', type=Path, required=True)
    parser.add_argument('--exclude-candidates', type=Path, action='append', default=[],
                        help='Subtract machine rows from completed candidate TSVs before selecting timeouts')
    parser.add_argument('--run-dir', type=Path, action='append', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source_cohort = set(read_rows(args.cohort))
    cohort = set(source_cohort)
    exclusions = []
    for path in args.exclude_candidates:
        with path.open() as source:
            reader = csv.DictReader(source, delimiter='\t')
            if 'machine' not in (reader.fieldnames or ()):
                raise ValueError(f'Candidate file lacks machine column: {path}')
            candidates = {row['machine'] for row in reader}
        removed = cohort & candidates
        exclusions.append({'path': str(path), 'sha256': digest(path),
                           'candidate_rows': len(candidates), 'newly_excluded_rows': len(removed)})
        cohort -= candidates
    eligible_rows = sorted(cohort, key=lambda m: hashlib.sha256(m.encode()).digest())
    eligible_sha256 = hashlib.sha256(encoded(eligible_rows).encode()).hexdigest()
    sources = []
    queues = {}
    for run in args.run_dir:
        manifest_path = run/'manifest.json'
        manifest = json.loads(manifest_path.read_text())
        selected = run/'selected.txt'
        remaining = read_rows(selected)
        if len(remaining) != manifest['selected_rows'] or digest(selected) != manifest['selected_sha256']:
            raise ValueError(f'Selected cohort changed: {run}')
        source = {'run_dir': str(run), 'manifest_sha256': digest(manifest_path), 'stages': []}
        for index, stage in enumerate(manifest['stages']):
            single = run/f'stage-{index:02d}.tsv'
            workers = manifest.get('workers', 1)
            logs = [(single, remaining)] if single.exists() else [
                (run/f'stage-{index:02d}-worker-{i:02d}.tsv', remaining[i::workers])
                for i in range(workers)]
            found = {}
            log_hashes = {}
            for path, shard in logs:
                before = digest(path) if path.exists() else None
                part = read_results(path, set(shard))
                if len(part) != len(shard):
                    raise ValueError(f'Incomplete source stage: {path}')
                if path.exists() and digest(path) != before:
                    raise ValueError(f'Source log changed while reading: {path}')
                found.update(part)
                log_hashes[path.name] = before
            eligible = {machine for machine in remaining
                        if machine in cohort and found[machine][0] == 'timeout'}
            normalized = {'bound': manifest['bound'], **stage, 'history': stage.get('history', 0)}
            key = json.dumps(normalized, sort_keys=True)
            queue = queues.setdefault(key, {'parameters': normalized, 'machines': set()})
            queue['machines'] |= eligible
            source['stages'].append({'stage': index, 'rows': len(remaining),
                                     'surviving_timeouts': len(eligible), 'log_sha256': log_hashes})
            remaining = [machine for machine in remaining if found[machine][0] != 'candidate']
        sources.append(source)
    outputs = {}
    summaries = []
    union = set()
    for key, queue in sorted(queues.items()):
        params = queue['parameters']
        rows = sorted(queue['machines'], key=lambda m: hashlib.sha256(m.encode()).digest())
        if not rows:
            continue
        name = params['mode']+'-'+hashlib.sha256(key.encode()).hexdigest()[:12]
        directory = args.output_dir/name
        content = encoded(rows)
        stage = {k: v for k, v in params.items() if k != 'bound'}
        if stage['mode'] == 'ng':
            del stage['history']
        selection = {'status': 'Search retry cohort: surviving timeouts, not proof claims.',
                     'not_accepted_rows': len(rows),
                     'not_accepted_sha256': hashlib.sha256(content.encode()).hexdigest(),
                     'parameters': params, 'source_cohort_sha256': digest(args.cohort),
                     'eligible_cohort_sha256': eligible_sha256, 'exclusions': exclusions}
        outputs[directory/'input.txt'] = content
        outputs[directory/'input.json'] = json.dumps(selection, indent=2, sort_keys=True)+'\n'
        outputs[directory/'stages.json'] = json.dumps([stage], indent=2, sort_keys=True)+'\n'
        summaries.append({'directory': str(directory), **selection})
        union.update(rows)
    union_rows = sorted(union, key=lambda m: hashlib.sha256(m.encode()).digest())
    report = {'status': 'Frozen timeout retry queues for search only; no new proof claims.',
              'source_cohort_path': str(args.cohort),
              'source_cohort_rows': len(source_cohort), 'source_cohort_sha256': digest(args.cohort),
              'eligible_rows': len(cohort), 'eligible_sha256': eligible_sha256,
              'exclusions': exclusions,
              'unique_timeout_rows': len(union), 'queued_attempts': sum(s['not_accepted_rows'] for s in summaries),
              'sources': sources, 'queues': summaries, 'generator_sha256': digest(Path(__file__)),
              'pipeline_helpers_sha256': digest(Path(__file__).with_name('pipeline_sweep.py')),
              'all_timeouts_sha256': hashlib.sha256(encoded(union_rows).encode()).hexdigest()}
    outputs[args.output_dir/'all-timeouts.txt'] = encoded(union_rows)
    outputs[args.output_dir/'eligible.txt'] = encoded(eligible_rows)
    outputs[args.report] = json.dumps(report, indent=2, sort_keys=True)+'\n'
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise ValueError(f'Retry queue output differs: {path}')
        else:
            if path.exists() and path.read_text() != content:
                raise ValueError(f'Refusing to replace a frozen retry queue; use a new output directory: {path}')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(f'{len(union)} surviving machines; {report["queued_attempts"]} queued per-stage attempts.')


if __name__ == '__main__':
    main()
