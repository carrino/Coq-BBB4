"""Export a completed prefix of a sweep while later stages continue.

This is search bookkeeping only. Every included stage must cover its complete
input, and the output records the original manifest and any driver continuation.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from pipeline_sweep import digest, encoded, read_rows, read_results

FIELDS = ('machine', 'stage', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--through', type=int, required=True, help='Last completed stage, zero based')
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    manifest_path = args.run_dir/'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    if not 0 <= args.through < len(manifest['stages']):
        raise ValueError('Invalid completed stage index')
    selected = args.run_dir/'selected.txt'
    rows = read_rows(selected)
    if digest(selected) != manifest['selected_sha256'] or len(rows) != manifest['selected_rows']:
        raise ValueError('Selected cohort differs from the run manifest')
    remaining = rows
    accepted = []
    results = []
    final_timeouts = []
    for index, stage in enumerate(manifest['stages'][:args.through+1]):
        single = args.run_dir/f'stage-{index:02d}.tsv'
        workers = manifest.get('workers', 1)
        if single.exists():
            logs = [(single, remaining)]
        else:
            logs = [(args.run_dir/f'stage-{index:02d}-worker-{i:02d}.tsv', remaining[i::workers])
                    for i in range(workers)]
        found = {}
        hashes = {}
        for path, shard in logs:
            before = digest(path) if path.exists() else None
            part = read_results(path, set(shard))
            if len(part) != len(shard):
                raise ValueError(f'Stage {index} incomplete: {len(part)}/{len(shard)} in {path}')
            if path.exists() and digest(path) != before:
                raise ValueError(f'Log changed while being read: {path}')
            hashes[path.name] = before
            found.update(part)
        statuses = Counter(status for status, _ in found.values())
        results.append({'stage': index, **stage, 'rows': len(remaining),
                        'statuses': dict(sorted(statuses.items())), 'log_sha256': hashes,
                        'sum_row_seconds': round(sum(seconds for _, seconds in found.values()), 6)})
        accepted += [{'machine': machine, 'stage': index, **stage,
                      'history': stage.get('history', 0), 'bound': manifest['bound']}
                     for machine in remaining if found[machine][0] == 'candidate']
        remaining = [machine for machine in remaining if found[machine][0] != 'candidate']
        final_timeouts = [machine for machine in remaining if found[machine][0] == 'timeout']
    candidates = '\t'.join(FIELDS)+'\n'+''.join(
        '\t'.join(str(row[field]) for field in FIELDS)+'\n' for row in accepted)
    report = {
        'status': 'Complete search checkpoint through the recorded stage; no new proof or census discharge claims.',
        'source_run_manifest_sha256': digest(manifest_path),
        'source_run_manifest': manifest, 'through_stage': args.through,
        'selected_rows': len(rows), 'results': results,
        'candidate_rows': len(accepted), 'not_accepted_rows': len(remaining),
        'final_stage_timeout_rows': len(final_timeouts),
        'candidate_tsv_sha256': hashlib.sha256(candidates.encode()).hexdigest(),
        'not_accepted_sha256': hashlib.sha256(encoded(remaining).encode()).hexdigest(),
        'final_stage_timeouts_sha256': hashlib.sha256(encoded(final_timeouts).encode()).hexdigest(),
        'exporter_sha256': digest(Path(__file__)),
    }
    provenance = args.run_dir/'prefix-provenance.json'
    if provenance.exists():
        report['execution_provenance'] = json.loads(provenance.read_text())
    outputs = {args.output_dir/'candidates.tsv': candidates,
               args.output_dir/'not-accepted.txt': encoded(remaining),
               args.output_dir/'timeouts.txt': encoded(final_timeouts),
               args.report: json.dumps(report, indent=2, sort_keys=True)+'\n'}
    for path, contents in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != contents:
                raise ValueError(f'Checkpoint output differs: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
    print(f'{len(accepted)} candidates; {len(remaining)} not accepted; {len(final_timeouts)} final-stage timeouts.')


if __name__ == '__main__':
    main()
