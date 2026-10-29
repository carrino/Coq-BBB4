"""Freeze compact candidates from a prefix of the fresh state search ledger.

This is untrusted scheduling and certificate transport. Only the separate Coq
replays establish bounds; successful native searches are never counted as proofs.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from check_closure_wave import FIELDS, machine_hash
from weighted_campaign_v2 import emit_bundles

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, data):
    if path.exists():
        raise ValueError('Refusing to replace frozen selection: '+str(path))
    path.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', required=True)
    parser.add_argument('--offset', type=int, default=0)
    parser.add_argument('--limit', type=int, default=0)
    parser.add_argument('--search-dir', type=Path,
                        default=ROOT/'build/burn2-state/weighted-w3-a4096')
    args = parser.parse_args()
    if (not args.prefix.startswith('burn2-state-') or
        not args.prefix.replace('-', '').isalnum() or args.offset < 0 or args.limit < 0):
        raise ValueError('Invalid new selection name or slice')
    input_path = ROOT/'research/burn2-state-input.txt'
    machines = input_path.read_text().splitlines()
    manifest_path = args.search_dir/'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    ledger = args.search_dir/'results.jsonl'
    all_rows = [json.loads(line) for line in ledger.read_text().splitlines()]
    if (manifest['input_sha256'] != sha(input_path) or
        [row['machine'] for row in all_rows] != machines[:len(all_rows)]):
        raise ValueError('Search ledger is not the exact frozen input prefix')
    stop = args.offset+args.limit if args.limit else len(all_rows)
    if not args.offset < stop <= len(all_rows):
        raise ValueError('Empty or incomplete selected slice')
    rows = all_rows[args.offset:stop]
    ordinary_ids = {row['machine'] for row in rows if any(
        orientation['status'] == 'ordinary_candidate'
        for orientation in row['orientations'])}
    weighted = [row for row in rows if row['candidate'] is not None and
                row['machine'] not in ordinary_ids]
    weighted.sort(key=lambda row: (len(row['candidate']['nodes']), row['machine']))
    selection = {'scope': 'Untrusted candidates; no kernel-checked claims.',
                 'input_sha256': sha(input_path), 'manifest_sha256': sha(manifest_path),
                 'results_sha256': sha(ledger), 'offset': args.offset,
                 'attempted_rows': len(rows), 'parameters': manifest['parameters'],
                 'producer_sha256': sha(Path(__file__))}
    registry = ROOT/'research'/(args.prefix+'-input.json')
    bundle_dir = ROOT/'research'/(args.prefix+'-certificates')
    ordinary_path = ROOT/'research'/(args.prefix+'-ordinary-input.json')
    summary_path = ROOT/'research'/(args.prefix+'-search.json')
    if any(path.exists() for path in (registry, bundle_dir, ordinary_path, summary_path)):
        raise ValueError('Selection outputs already exist')
    if weighted:
        emit_bundles(weighted, bundle_dir, registry, selection)
    params = manifest['parameters']
    ordinary = sorted((dict(machine=machine, mode='ng', bound=4096,
                            size=params['width'], anchor=params['anchor'],
                            fuel=params['fuel'], extra=params['rounds'], history=0)
                       for machine in ordinary_ids), key=machine_hash)
    if ordinary:
        save(ordinary_path, {'selection': selection, 'search_sources': [],
                            'excluded_ledgers_sha256': {}, 'columns': FIELDS,
                            'selected_rows': len(ordinary),
                            'rows': [[row[key] for key in FIELDS] for row in ordinary]})
    statuses = Counter(orientation['status'] for row in rows
                       for orientation in row['orientations'])
    diagnostics = Counter()
    for row in rows:
        diagnostics.update(row['diagnostics'])
    save(summary_path, {**selection, 'weighted_state_candidates': len(weighted),
                        'ordinary_both_candidates': len(ordinary),
                        'not_accepted_rows': len(rows)-len(weighted)-len(ordinary),
                        'orientation_statuses': dict(statuses),
                        'diagnostics': dict(diagnostics), 'kernel_checked_rows': 0})
    print(json.dumps({'weighted_state_candidates': len(weighted),
                      'ordinary_both_candidates': len(ordinary), 'attempted': len(rows)}))


if __name__ == '__main__':
    main()
