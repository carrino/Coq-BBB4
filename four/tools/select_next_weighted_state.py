"""Extract exactly the exclusive state-only residual weighted certificates.

Selection is scheduling evidence only. check_next_weighted_state.py must replay
every recurrence, pending-membership and exact-inventory obligation in Coq.
"""
import csv
import json
from pathlib import Path

from check_weighted_state import ROOT, load_input, sha
from weighted_codec_v2 import bundle_encode


def main():
    summary_path = ROOT / 'research/campaign-next-summary.json'
    summary = json.loads(summary_path.read_text())
    queue_path = ROOT / summary['outputs']['queued.tsv']['path']
    if sha(queue_path) != summary['outputs']['queued.tsv']['sha256']:
        raise ValueError('Queue does not match the frozen scheduling summary')
    with queue_path.open() as stream:
        queue = list(csv.DictReader(stream, delimiter='\t'))
    selected = [row for row in queue if
                'weighted.state_search' in row['state_sources'].split(',')]
    if len(selected) != 240 or any(row['state_sources'] != 'weighted.state_search'
                                   or row['both_sources']
                                   or row['state_already_checked'] != 'no'
                                   for row in selected):
        raise ValueError('Expected exactly 240 exclusive state-only residuals')
    wanted = {row['machine'] for row in selected}
    source_path = ROOT / 'research/weighted-state-search-input.json'
    rows, sources = load_input(source_path)
    chosen = sorted((row for row in rows if row['machine'] in wanted),
                    key=lambda row: (len(row['nodes']), row['machine']))
    if len(chosen) != 240 or {row['machine'] for row in chosen} != wanted:
        raise ValueError('Residual certificate inventory is incomplete')
    out = ROOT / 'research/next-weighted-state-certificates.json'
    out.write_text(bundle_encode(chosen))
    sources.update({str(p.relative_to(ROOT)): sha(p)
                    for p in (summary_path, queue_path, Path(__file__))})
    manifest = {
        'format': 'BBB24 compact weighted certificates v2',
        'rows': len(chosen),
        'bundles': [{'path': str(out.relative_to(ROOT)), 'rows': len(chosen),
                     'bytes': out.stat().st_size, 'sha256': sha(out)}],
        'scope': 'State-only; no instruction-bound claim.',
        'status': 'Untrusted candidates; kernel replay and exact inventory required.',
        'ordering': 'Increasing graph node count, then lexicographic machine ID.',
        'selection': {'queue_source': 'weighted.state_search',
                      'exclusive_state_only_rows': 240,
                      'source_sha256': sources}}
    (ROOT / 'research/next-weighted-state-input.json').write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print('Extracted exactly 240 exclusive state-only weighted candidates.')


if __name__ == '__main__':
    main()
