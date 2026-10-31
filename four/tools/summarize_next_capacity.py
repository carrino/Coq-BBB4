"""Validate frozen discovery provenance and separately audited pilot inventories."""
import argparse
import csv
import hashlib
import json
from pathlib import Path

import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / 'research/next-capacity'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def read(suffix):
    return json.loads(path(suffix).read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--preflight', action='store_true',
                        help='Check all discovery sources and the native binary only')
    args = parser.parse_args()
    manifest = read('manifest.json')
    for group in ('sources_sha256', 'solver_sources_sha256'):
        for name, digest in manifest[group].items():
            require(sha(ROOT / name) == digest, 'Changed discovery source: ' + name)
    require(sha(ROOT / 'build/weighted-v2/dump') == manifest['binary_sha256'],
            'Changed native graph producer')
    require(sha(path('input.txt')) == manifest['input_sha256'], 'Changed sample input')
    if args.preflight:
        print('Discovery sources, binary and sample hashes match; no proof claim.')
        return
    search = read('search-report.json')
    require(sha(path('manifest.json')) == search['manifest_sha256'], 'Changed search manifest')
    ledger = ROOT / 'build/next-capacity/results.jsonl'
    require(sha(ledger) == search['ledger_sha256'], 'Changed search ledger')
    rows = [json.loads(line) for line in ledger.read_text().splitlines()]
    require([row['machine'] for row in rows] == path('input.txt').read_text().splitlines(),
            'Ledger does not cover the exact complete input')
    both = set((ROOT / 'build/campaign-final/both-unproved-initial-cohort.txt').read_text().splitlines())
    state = set((ROOT / 'build/campaign-final/state-unproved-initial-cohort.txt').read_text().splitlines())
    with (ROOT / 'build/campaign-next/queued.tsv').open() as stream:
        queue = {row['machine'] for row in csv.DictReader(stream, delimiter='\t')}
    exact = read('inventory-check.json')
    for name, digest in exact['inputs_sha256'].items():
        require(sha(ROOT / name) == digest, 'Changed exact-inventory input: ' + name)
    exact_receipt_path = ROOT / exact['kernel_receipt']
    require(sha(exact_receipt_path) == exact['kernel_receipt_sha256'],
            'Changed exact-inventory kernel receipt')
    exact_receipt = kernel_audit_cache._load_receipt(exact_receipt_path)
    require(exact_receipt['kind'] == 'recursive' and exact_receipt['result'] == 'passed',
            'Exact inventories require a full recursive kernel audit')
    for name, module in exact_receipt['snapshot']['graph'].items():
        require(sha(Path(module['source'])) == module['source_sha256'], 'Changed exact-inventory source: ' + name)
        require(sha(Path(module['object'])) == module['object_sha256'], 'Changed exact-inventory object: ' + name)
    exact_descriptors = {board['id']: board for board in exact['boards']}
    boards, checked = [], set()
    for kind, namespace in (('capacity', 'BBB24NextCapacity'), ('portfolio', 'BBB24NextPortfolio')):
        report_path = path(kind + '-check.json')
        report = json.loads(report_path.read_text())
        inventory_path = path(kind + '-checked-machines.json')
        require(sha(inventory_path) == report['inventory_sha256'], 'Changed checked inventory')
        ids = {row['machine'] for row in json.loads(inventory_path.read_text())['rows']}
        expected = {row['candidate']['machine'] for row in rows
                    if (row.get('candidate') or {}).get('kind') == kind}
        require(ids == expected, 'Audited inventory differs from discovery candidates')
        require(report['census_linked'] == len(ids) and report['counts'] == {'coq_checked': len(ids)},
                'Incomplete proof check')
        directory = ROOT / 'build/next-capacity' / (kind + '-proof')
        for name, digest in report['artifacts_sha256'].items():
            require(sha(directory / name) == digest, 'Changed proof artifact: ' + name)
        require(report['manifest']['registry_sha256'] == sha(path(kind + '-registry.json')),
                'Changed proof certificate registry')
        registry = read(kind + '-registry.json')
        for bundle in registry['bundles']:
            require(sha(ROOT / bundle['path']) == bundle['sha256'], 'Changed compact certificate')
        for name, digest in report['manifest']['sources_sha256'].items():
            require(sha(ROOT / name) == digest, 'Changed checker source: ' + name)
        receipt_path = directory / 'kernel-audit.json'
        receipt = kernel_audit_cache._load_receipt(receipt_path)
        require(receipt['kind'] == 'recursive' and receipt['result'] == 'passed',
                'Missing successful recursive kernel audit')
        require(namespace + '.WeightedAll' in receipt['checked_modules'], 'Wrong audited board')
        for name, module in receipt['snapshot']['graph'].items():
            require(sha(Path(module['source'])) == module['source_sha256'], 'Changed audited source: ' + name)
            require(sha(Path(module['object'])) == module['object_sha256'], 'Changed audited object: ' + name)
        require(not (checked & ids), 'Overlapping new boards')
        checked |= ids
        descriptor = exact_descriptors['next_' + kind]
        require(descriptor['module'] in exact_receipt['checked_modules'], 'Wrong exact-inventory audit root')
        require(descriptor['rows'] == len(ids) and descriptor['scope'] == 'both', 'Wrong exact-inventory scope')
        boards.append({'kind': kind, 'checked_rows': len(ids),
                       'report': str(report_path.relative_to(ROOT)), 'report_sha256': sha(report_path),
                       'inventory': str(inventory_path.relative_to(ROOT)), 'inventory_sha256': sha(inventory_path),
                       'kernel_receipt': str(receipt_path.relative_to(ROOT)),
                       'kernel_receipt_sha256': sha(receipt_path), 'descriptor': descriptor})
    require(checked <= both and not (checked & queue), 'New audited IDs overlap previous work')
    require(checked == set(search['incremental_unique_candidate_ids']), 'Unreplayed candidates remain')
    summary = {
        'scope': 'Audited local increment to the frozen campaign baseline; no global census claim.',
        'search_report': str(path('search-report.json').relative_to(ROOT)),
        'search_report_sha256': sha(path('search-report.json')),
        'exact_inventory_report': str(path('inventory-check.json').relative_to(ROOT)),
        'exact_inventory_report_sha256': sha(path('inventory-check.json')),
        'summary_producer_sha256': sha(Path(__file__)),
        'sample_rows': len(rows), 'graphs_solved': search['counts'].get('graphs_solved', 0),
        'candidate_count': search['incremental_unique_candidates'],
        'checked_incremental_unique_both': len(checked),
        'checked_incremental_unique_state': len(checked & state),
        'new_both_ids': sorted(checked), 'new_state_ids': sorted(checked & state),
        'baseline_both_residual': len(both), 'baseline_state_residual': len(state),
        'both_residual_after_this_increment_only': len(both - checked),
        'state_residual_after_this_increment_only': len(state - checked),
        'queue_overlap': len(checked & queue),
        'search_resource_outcomes': {
            'worker_failures': search['counts'].get('worker_failure', 0),
            'machine_wall_timeouts': search['counts'].get('machine_wall_timeout', 0),
            'lp_target_timeouts': search['counts'].get('target_timeouts', 0),
            'native_closed_partial_graphs_retained':
                search['counts'].get('graph_status_closed_partial', 0),
            'search_worker_address_space_limit_bytes': manifest['parameters']['address_space_bytes'],
            'proof_worker_address_space_limit_bytes': 2147483648,
            'python_worker_peak_rss_kib_excluding_native_child': search['maximum_worker_rss_kib']},
        'boards': boards}
    path('summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: summary[key] for key in ('sample_rows', 'candidate_count',
        'checked_incremental_unique_both', 'checked_incremental_unique_state')}))


if __name__ == '__main__':
    main()
