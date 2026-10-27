"""Reproduce the BBB(2,4) burndown from the fixed 256-step survey.

First run triage.py. Compact tracked outputs are a 1,024-row sample ledger and
a summary; --inventory also exports all residual families under ignored build/.
This is bookkeeping, not a proof checker. Checked status comes only from the
explicit, source-hashed proof registry, never from a search verdict.
"""
import argparse
import csv
import hashlib
import io
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIELDS = ['status', 'reason', 'machine', 'root', 'free_cells',
          'family_weight', 'total_completion_weight', 'root_multiplier', 'state_bound',
          'instruction_bound', 'proof', 'census_linked']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ledger_row(machine, result, verified):
    require(re.fullmatch(r'(?:---|[0-3][LR][AB]){4}_(?:---|[0-3][LR][AB]){4}', machine),
            f'Invalid two-state, four-symbol table: {machine}')
    require(machine[:3] in ('0LB', '1LB'), f'Unexpected root: {machine}')
    root = 'blank' if machine.startswith('0LB') else 'nonblank'
    row = dict.fromkeys(FIELDS, '')
    row.update(machine=machine, root=root, free_cells=machine.count('---'),
               family_weight=17**machine.count('---'),
               total_completion_weight=16**machine.count('---'),
               root_multiplier=2 if root == 'blank' else 6, census_linked='no')
    if result is None:
        row['status'] = 'not_sampled'
    elif result['status'] == 'irules':
        row['status'] = 'candidate_unchecked'
    else:
        require(result['status'] == 'undecided', 'Unexpected search status')
        row.update(status='no_certificate', reason=result[None][0].split()[0])
    if machine in verified['machines']:
        require(row['status'] == 'candidate_unchecked', 'Checked example missing from candidates')
        row.update(status='coq_checked', state_bound=verified['state_bound'],
                   instruction_bound=verified['instruction_bound'],
                   proof='BBB24.AffineExamples.completions_' + machine.replace('-', 'X'))
    return row


def tsv(rows):
    out = io.StringIO()
    writer = csv.DictWriter(out, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--survey-dir', type=Path, default=ROOT/'build/triage')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--inventory', action='store_true')
    args = parser.parse_args()
    report = json.loads((ROOT/'research/triage-256.json').read_text())
    verified = json.loads((ROOT/'research/burndown-verified.json').read_text())
    require(digest(ROOT/verified['proof_source']) == verified['proof_source_sha256'],
            'Proof source changed: audit it before updating the verified registry')
    source = (ROOT/verified['proof_source']).read_text()
    for machine in verified['machines']:
        require('Theorem completions_' + machine.replace('-', 'X') + ' :' in source,
                f'Missing completion theorem for {machine}')

    sample_path = args.survey_dir/'sample.txt'
    require(digest(sample_path) == report['sample_sha256'], 'Sample does not match baseline')
    sample = sample_path.read_text().splitlines()
    with (args.survey_dir/'irules.csv').open() as f:
        results = list(csv.DictReader(f))
    require(len(results) == len(sample) == len(set(sample)), 'Duplicate or missing sample rows')
    by_machine = {r['machine']: r for r in results}
    require(set(by_machine) == set(sample), 'Search output has missing or extra machines')
    require(Counter(r['status'] for r in results) == report['baseline']['statuses'],
            'Search statuses differ from baseline; update the baseline explicitly')
    sampled = [ledger_row(m, by_machine[m], verified) for m in sample]
    require(Counter(r['reason'] for r in sampled if r['status'] == 'no_certificate') ==
            report['baseline']['unresolved_reasons'], 'Failure reasons differ from baseline')
    require(set(verified['machines']) <= set(sample), 'Verified registry is outside this sample')

    roots, seen, all_statuses = {}, set(), Counter()
    inventories = []
    for label, root_class in report['root_classes'].items():
        path = args.survey_dir/f'{label}.unresolved.txt'
        machines = path.read_text().splitlines()
        require(len(machines) == len(set(machines)), f'Duplicate {label} family')
        require(not seen.intersection(machines), 'Overlapping root inventories')
        seen.update(machines)
        rows = [ledger_row(m, by_machine.get(m), verified) for m in machines]
        require(all(r['root'] == label for r in rows), f'Wrong root in {label} inventory')
        weight = sum(r['family_weight'] for r in rows)
        total_weight = sum(r['total_completion_weight'] for r in rows)
        require(len(rows) == report['roots'][label]['leaves']['unresolved'], 'Family count changed')
        require(weight == report['roots'][label]['weighted']['unresolved'], 'Family weight changed')
        all_statuses.update(r['status'] for r in rows)
        roots[label] = dict(families=len(rows), family_weight=weight,
                            total_completion_weight=total_weight,
                            root_multiplier=root_class['multiplicity'],
                            raw_table_weight=weight*root_class['multiplicity'],
                            raw_total_table_weight=total_weight*root_class['multiplicity'],
                            inventory_sha256=digest(path))
        if args.inventory:
            inventories.extend(rows)
    require(set(sample) <= seen, 'Sample contains a family outside the inventory')
    require(sum(r['raw_table_weight'] for r in roots.values()) == report['raw_unresolved_weight'],
            'Total unresolved weight changed')
    summary = dict(
        baseline='256-step exploratory survey; four separately checked affine families',
        families=len(seen), raw_table_weight=report['raw_unresolved_weight'], roots=roots,
        raw_total_table_weight=sum(r['raw_total_table_weight'] for r in roots.values()),
        status_counts=dict(sorted(all_statuses.items())),
        sample_size=len(sample), sample_status_counts=dict(sorted(Counter(r['status'] for r in sampled).items())),
        sample_no_certificate_reasons=report['baseline']['unresolved_reasons'],
        state_checked=len(verified['machines']), instruction_checked=len(verified['machines']),
        census_linked=0, sample_sha256=report['sample_sha256'],
        search_csv_sha256=digest(args.survey_dir/'irules.csv'),
        verified_registry_sha256=digest(ROOT/'research/burndown-verified.json'))
    sampled.sort(key=lambda r: (r['status'], r['reason'], r['machine']))
    outputs = {'burndown-sample.tsv': tsv(sampled),
               'burndown-summary.json': json.dumps(summary, indent=2)+'\n'}
    for name, data in outputs.items():
        path = ROOT/'research'/name
        if args.check:
            require(path.read_text() == data, f'{name} is stale')
        else:
            path.write_text(data)
    if args.inventory:
        path = ROOT/'build/burndown-inventory.tsv'
        path.parent.mkdir(exist_ok=True)
        with path.open('w') as f:
            writer = csv.DictWriter(f, FIELDS, delimiter='\t', lineterminator='\n')
            writer.writeheader()
            writer.writerows(inventories)
        print(f'Full inventory: {path}')
    print(json.dumps(summary['status_counts'], sort_keys=True))


if __name__ == '__main__':
    main()
