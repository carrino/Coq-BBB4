"""Check targeted refinement evidence and count exact new family IDs."""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path

import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / 'research/burn2-capacity'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(name):
    return PREFIX.with_name(PREFIX.name + '-' + name)


def read(name):
    return json.loads(path(name).read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    manifest, search, exact = [read(name) for name in
                               ('manifest.json', 'search-report.json', 'inventory-check.json')]
    for document in (manifest, exact):
        for name, digest in document.get('sources_sha256', document.get('inputs_sha256')).items():
            require(sha(ROOT / name) == digest, 'Changed pinned input: ' + name)
    require(sha(path('manifest.json')) == search['manifest_sha256'], 'Changed discovery manifest')
    ledger = ROOT / 'build/burn2-capacity/results.jsonl'
    require(sha(ledger) == search['ledger_sha256'], 'Changed discovery ledger')
    rows = [json.loads(line) for line in ledger.read_text().splitlines()]
    require([row['machine'] for row in rows] == manifest['machines'], 'Incomplete discovery inventory')
    candidates = {row['machine']: row['candidate'] for row in rows if row.get('candidate')}
    both = set((ROOT / 'build/next-burndown/both-remaining.txt').read_text().splitlines())
    state = set((ROOT / 'build/next-burndown/state-remaining.txt').read_text().splitlines())
    with (ROOT / 'build/next-burndown/queued.tsv').open() as stream:
        queue = {row['machine'] for row in csv.DictReader(stream, delimiter='\t')}
    receipt_path = ROOT / exact['kernel_receipt']
    require(sha(receipt_path) == exact['kernel_receipt_sha256'], 'Changed kernel receipt')
    receipt = kernel_audit_cache._load_receipt(receipt_path)
    require(receipt['kind'] == 'recursive' and receipt['result'] == 'passed', 'Missing complete audit')
    for name, module in receipt['snapshot']['graph'].items():
        require(sha(Path(module['source'])) == module['source_sha256'], 'Changed audited source: ' + name)
        require(sha(Path(module['object'])) == module['object_sha256'], 'Changed audited object: ' + name)
    checked, boards = set(), []
    for descriptor in exact['boards']:
        kind = descriptor['id'].removeprefix('burn2_capacity_')
        report, registry = read(kind + '-check.json'), read(kind + '-registry.json')
        inventory_path = path(kind + '-checked-machines.json')
        inventory = json.loads(inventory_path.read_text())
        machines = [row['machine'] for row in inventory['rows']]
        ids = set(machines)
        require(len(ids) == len(machines) == descriptor['rows'], 'Wrong exact inventory size')
        require(ids == {machine for machine, candidate in candidates.items() if candidate['kind'] == kind},
                'Candidates and proved inventory differ')
        require(sha(inventory_path) == report['inventory_sha256'], 'Changed checked inventory')
        require(report['counts'] == {'coq_checked': len(ids)} and report['census_linked'] == len(ids),
                'Incomplete proof report')
        require(descriptor['module'] in receipt['checked_modules'], 'Unaudited inventory wrapper')
        require(descriptor['scope'] == 'both' and descriptor['state_bound'] ==
                descriptor['instruction_bound'] == 4096, 'Unexpected claim')
        require(sha(path(kind + '-registry.json')) == report['manifest']['registry_sha256'],
                'Changed registry')
        for bundle in registry['bundles']:
            require(sha(ROOT / bundle['path']) == bundle['sha256'], 'Changed compact certificates')
        for name, digest in report['manifest']['sources_sha256'].items():
            require(sha(ROOT / name) == digest, 'Changed proof source: ' + name)
        require(not (checked & ids), 'Duplicate family across boards')
        checked |= ids
        boards.append({'kind': kind, 'rows': len(ids), 'descriptor': descriptor,
                       'report_sha256': sha(path(kind + '-check.json')),
                       'inventory_sha256': sha(inventory_path)})
    require(checked == set(candidates), 'Unproved candidates remain')
    require(checked <= both and not (checked & queue), 'Overlap with previous work')
    counts = Counter()
    for row in rows:
        counts.update(row.get('counts', {}))
    summary = {
        'scope': 'Kernel-audited local increment to the first supplement; global upper bound remains open.',
        'summary_producer_sha256': sha(Path(__file__)),
        'baseline_summary_sha256': sha(ROOT / 'research/next-burndown-summary.json'),
        'search_report_sha256': sha(path('search-report.json')),
        'inventory_report_sha256': sha(path('inventory-check.json')),
        'sample_rows': len(rows), 'candidate_count': len(candidates),
        'checked_incremental_unique_both': len(checked),
        'checked_incremental_unique_state': len(checked & state),
        'new_both_ids': sorted(checked), 'new_state_ids': sorted(checked & state),
        'baseline_both_residual': len(both), 'baseline_state_residual': len(state),
        'both_residual_after_this_increment_only': len(both - checked),
        'state_residual_after_this_increment_only': len(state - checked),
        'queue_overlap': len(checked & queue), 'search_counts': dict(counts),
        'kernel_modules': len(receipt['snapshot']['graph']), 'boards': boards}
    text = json.dumps(summary, indent=2, sort_keys=True) + '\n'
    output = path('summary.json')
    if args.check:
        require(output.read_text() == text, 'Published summary differs')
    elif output.exists() and output.read_text() != text:
        raise ValueError('Refusing to overwrite changed published summary')
    else:
        output.write_text(text)
    print(json.dumps({k: summary[k] for k in ('sample_rows', 'candidate_count',
                      'checked_incremental_unique_both', 'checked_incremental_unique_state')}))


if __name__ == '__main__':
    main()
