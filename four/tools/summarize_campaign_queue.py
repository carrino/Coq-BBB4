"""Intersect four existing candidate classes with the audited final campaign.

This schedules replay; it does not prove that a candidate will be accepted.
The published report is gated on the final campaign report and exact agreement
with its inventories, ledgers, residuals, counts, and recorded source hashes.
"""
import argparse
from collections import defaultdict
import csv
import hashlib
import io
from itertools import combinations
import json
from pathlib import Path

from check_campaign import CHAMPION, ROOT, ledger, load_manifest, read_inventory, sha
from check_closure_wave import load_input
from generate_pipeline_examples import codes
from weighted_codec_v2 import bundle_decode

REPO = ROOT.parent
CLASSES = {'rw': ('both', 4176), 'timeout': ('both', 2184),
           'weighted_full': ('both', 19950), 'weighted_state': ('state', 1203)}


def rel(path):
    return str(path.resolve().relative_to(ROOT))


def text_hash(text):
    return hashlib.sha256(text.encode()).hexdigest()


def json_hash(data):
    return text_hash(json.dumps(data, separators=(',', ':'), sort_keys=True))


def machine_text(machines):
    return ''.join(machine+'\n' for machine in sorted(machines))


def fixed(path, text, check):
    if path.exists():
        if path.read_text() != text:
            raise ValueError(f'Frozen queue artifact differs: {path}')
    elif check:
        raise ValueError(f'Missing queue artifact: {path}')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def read_candidates():
    roots, verified, catalog = {}, {}, {}
    classes = {name: set() for name in CLASSES}
    references = defaultdict(set)

    def pin(path, expected=None, root=False):
        value = sha(path)
        if expected is not None and value != expected:
            raise ValueError(f'Candidate source hash changed: {path}')
        previous = verified.setdefault(rel(path), value)
        if previous != value:
            raise ValueError(f'Candidate source changed during collection: {path}')
        if root:
            roots[rel(path)] = value
        return value

    def add(name, kind, path, weighted=False):
        pin(path, root=True)
        if weighted:
            registry = json.loads(path.read_text())
            machines = []
            for bundle in registry['bundles']:
                source = ROOT/bundle['path']
                pin(source, bundle['sha256'])
                rows = bundle_decode(source.read_text())
                if len(rows) != bundle['rows']:
                    raise ValueError('Weighted bundle row count changed')
                machines.extend(row['machine'] for row in rows)
            if len(machines) != registry['rows']:
                raise ValueError('Weighted registry row count changed')
        else:
            data, rows = load_input(path.resolve())
            machines = [row['machine'] for row in rows]
            for source in data['search_sources']:
                pin(REPO/source['report'], source['report_sha256'])
            for source, expected in data['excluded_ledgers_sha256'].items():
                pin(REPO/source, expected)
        if len(machines) != len(set(machines)) or classes[kind] & set(machines):
            raise ValueError(f'Duplicate candidate within class {kind}')
        for machine in machines:
            codes(machine)
            references[machine].add(name)
        classes[kind].update(machines)
        catalog[name] = {'class': kind, 'file': rel(path), 'rows': len(machines)}
        pin(path, roots[rel(path)])

    for batch in range(30):
        add(f'rw.batch{batch:03d}', 'rw', ROOT/f'research/repwl-stream/batch{batch:03d}-proof-input.json')
    add('rw.cpu_pilot', 'rw', ROOT/'research/repwl-cpu-pilot64-proof-input.json')
    add('rw.anchor_pilot', 'rw', ROOT/'research/repwl-anchor-proof-input.json')
    add('timeout.recovery', 'timeout', ROOT/'research/wave3-timeout-proof-input.json')
    end = 0
    weighted_input_hash = None
    for batch in range(30):
        path = ROOT/f'research/weighted-full-snapshots/batch{batch:03d}/registry.json'
        add(f'weighted.batch{batch:03d}', 'weighted_full', path, weighted=True)
        source = json.loads(path.read_text())['source']
        start, next_end = source['input_range']
        if start != end or next_end <= start or source['input_rows'] != 59627:
            raise ValueError('Weighted snapshots are not the expected complete cohort')
        if weighted_input_hash is not None and source['input_sha256'] != weighted_input_hash:
            raise ValueError('Weighted snapshot cohorts differ')
        weighted_input_hash, end = source['input_sha256'], next_end
    if end != 59627:
        raise ValueError('Weighted snapshots do not cover the full input')
    add('weighted.state_search', 'weighted_state', ROOT/'research/weighted-state-search-input.json', weighted=True)
    for name, (_, expected) in CLASSES.items():
        if len(classes[name]) != expected:
            raise ValueError(f'Candidate class count changed: {name}')
    for name, expected in verified.items():
        if sha(ROOT/name) != expected:
            raise ValueError(f'Candidate source changed during decoding: {name}')
    return classes, references, catalog, roots, verified


def verify_campaign(path, manifest, boards, manifest_inputs, cohort, checked, ledgers):
    if not path.is_file():
        raise ValueError('Final audited campaign report is not available; use --preview without publishing')
    digest = sha(path)
    report = json.loads(path.read_text())
    for key, expected in manifest_inputs.items():
        if report['inputs'].get(key) != expected:
            raise ValueError(f'Audited campaign inventory differs: {key}')
    for group in ('inputs', 'source_sha256'):
        for name, expected in report[group].items():
            if sha(ROOT/name) != expected:
                raise ValueError(f'Audited campaign {group} hash changed: {name}')
    if report['source_rows'] != {board['id']: len(board['machines']) for board in boards}:
        raise ValueError('Audited campaign board counts differ')
    if report.get('global_upper_bound_proved') is not False or not report.get('validation'):
        raise ValueError('Unexpected campaign validation/scope metadata')
    # The report preserves historical run metadata across clean replays. Check
    # this run's receipts locally, without putting local artifact identities in
    # the portable, deterministic queue summary.
    audit_path = (ROOT/report['ledgers']['both']['path']).parent/'latest-audit.json'
    if not audit_path.is_file():
        raise ValueError('Current campaign audit metadata is unavailable')
    audit = json.loads(audit_path.read_text())
    for phase in [audit, *audit.get('phases', [])]:
        receipt_path = ROOT/phase['receipt']
        if sha(receipt_path) != phase['receipt_sha256']:
            raise ValueError('Current campaign audit receipt changed')
        receipt = json.loads(receipt_path.read_text())
        if (receipt.get('result') != 'passed' or receipt.get('kind') != phase['kind'] or
                len(receipt['checked_modules']) != phase['checked_modules'] or
                len(receipt['reused_modules']) != phase['reused_modules']):
            raise ValueError('Current campaign audit receipt metadata disagrees')
    for scope in ('both', 'state'):
        if report[f'{scope}_census_linked_families'] != len(checked[scope]):
            raise ValueError('Audited distinct-family count differs')
        inventory = report['ledgers'][scope]
        actual = ROOT/inventory['path']
        if sha(actual) != inventory['sha256'] or actual.read_text() != ledgers[scope]:
            raise ValueError('Audited ledger differs from the exact manifest inventory')
        residual = cohort-checked[scope]
        recorded = report['initial_search_cohort'][scope]
        if (recorded['cohort_rows'] != len(cohort) or recorded['unproved'] != len(residual) or
                recorded['proved'] != len(cohort & checked[scope])):
            raise ValueError('Audited comparison-cohort counts differ')
        actual = ROOT/recorded['unproved_path']
        if sha(actual) != recorded['unproved_sha256'] or actual.read_text() != machine_text(residual):
            raise ValueError('Audited residual inventory differs')
    if sha(path) != digest:
        raise ValueError('Audited campaign report changed during verification')
    return {'report': rel(path), 'report_sha256': digest,
            'inputs_sha256': json_hash(report['inputs']),
            'proof_sources_sha256': json_hash(report['source_sha256']),
            'module': report['module'], 'validation': report['validation']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'research/campaign-final-input.json')
    parser.add_argument('--campaign-report', type=Path, default=ROOT/'research/campaign-final-summary.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/campaign-next-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/campaign-next')
    parser.add_argument('--preview', action='store_true', help='Print preliminary counts without writing queue artifacts')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.preview and args.check:
        parser.error('--preview and --check are mutually exclusive')
    helpers = [Path(__file__), ROOT/'tools/check_campaign.py', ROOT/'tools/check_closure_wave.py',
               ROOT/'tools/generate_pipeline_examples.py', ROOT/'tools/weighted_codec_v2.py']
    helper_hashes = {rel(path): sha(path) for path in helpers}
    manifest, boards, _, manifest_inputs = load_manifest(args.manifest)
    if len(boards) != 113:
        raise ValueError('Expected the frozen final 113-board campaign')
    cohort = set(read_inventory(manifest['cohort']))
    checked, ledgers = {}, {}
    for scope in ('both', 'state'):
        families, ledgers[scope] = ledger(boards, scope)
        checked[scope] = set(families)
    if not checked['both'] <= checked['state']:
        raise ValueError('State coverage must include every both-bound board')
    residual = {scope: cohort-checked[scope] for scope in checked}
    campaign = None if args.preview else verify_campaign(args.campaign_report, manifest, boards,
                                                        manifest_inputs, cohort, checked, ledgers)
    classes, references, catalog, source_files, verified = read_candidates()
    eligible = {name: {'both': (machines & residual['both']) if CLASSES[name][0] == 'both' else set(),
                      'state': machines & residual['state']} for name, machines in classes.items()}
    queued = {scope: set().union(*(value[scope] for value in eligible.values())) for scope in ('both', 'state')}
    totals = {'both_queue_rows': len(queued['both']), 'state_queue_rows': len(queued['state']),
              'unique_queued_machine_rows': len(queued['both'] | queued['state']),
              'both_and_state_rows': len(queued['both'] & queued['state']),
              'instruction_only_rows': len(queued['both']-queued['state']),
              'state_only_certificate_rows': len(queued['state']-queued['both'])}
    counts = {name: {'scope': CLASSES[name][0], 'candidate_rows': len(machines),
                    'outside_original_cohort_rows': len(machines-cohort),
                    'already_checked_both_rows': len(machines & checked['both']),
                    'already_checked_state_rows': len(machines & checked['state']),
                    'both_queue_rows': len(eligible[name]['both']) if CLASSES[name][0] == 'both' else None,
                    'state_queue_rows': len(eligible[name]['state'])} for name, machines in classes.items()}
    conditional = {'assumption': 'Every listed queued certificate is accepted by independent kernel replay and census discharge; this is not an audited reduction.',
                   'both_remaining_rows': len(residual['both']-queued['both']),
                   'state_remaining_rows': len(residual['state']-queued['state'])}
    short = {'preliminary': args.preview, 'board_count': len(boards),
             'audited_residual_rows' if not args.preview else 'manifest_residual_rows':
                 {scope: len(value) for scope, value in residual.items()},
             'classes': counts, 'totals': totals, 'conditional_after_all_replay': conditional}
    if args.preview:
        print(json.dumps(short, indent=2, sort_keys=True))
        return
    fields = ['machine', 'state_already_checked', 'both_sources', 'state_sources']
    table = io.StringIO()
    writer = csv.DictWriter(table, fields, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    source_queue_counts = {name: {'both': 0, 'state': 0} for name in catalog}
    for machine in sorted(queued['both'] | queued['state']):
        names = {}
        for scope in ('both', 'state'):
            names[scope] = sorted(name for name in references[machine]
                                  if machine in eligible[catalog[name]['class']][scope])
            for name in names[scope]:
                source_queue_counts[name][scope] += 1
        writer.writerow({'machine': machine, 'state_already_checked': 'yes' if machine in checked['state'] else 'no',
                         'both_sources': ','.join(names['both']), 'state_sources': ','.join(names['state'])})
    outputs = {'queued.tsv': table.getvalue(), 'both-pending.txt': machine_text(queued['both']),
               'state-pending.txt': machine_text(queued['state'])}
    for name in catalog:
        catalog[name]['queued_rows'] = source_queue_counts[name]
    source_files.update(helper_hashes)
    overlaps = [{'classes': [a, b], 'candidate_rows': len(classes[a] & classes[b]),
                 'both_queue_rows': len(eligible[a]['both'] & eligible[b]['both']),
                 'state_queue_rows': len(eligible[a]['state'] & eligible[b]['state'])}
                for a, b in combinations(CLASSES, 2)]
    report = {**short,
              'status': 'Replay scheduling only; no new proof claims or changes to the audited residual.',
              'scope': 'Distinct IDs from the original frozen comparison cohort. State-only candidates never enter the both/instruction queue.',
              'campaign': {**campaign, 'manifest': rel(args.manifest), 'manifest_sha256': sha(args.manifest),
                           'cohort_rows': len(cohort), 'cohort_machine_text_sha256': manifest['cohort']['machine_text_sha256']},
              'candidate_class_union_rows': len(set().union(*classes.values())),
              'pairwise_overlaps': overlaps, 'candidate_sources': catalog,
              'source_files_sha256': source_files,
              'verified_transitive_candidate_files': len(verified),
              'verified_transitive_candidate_hashes_sha256': json_hash(verified),
              'champion_candidate_classes': [name for name, machines in classes.items() if CHAMPION in machines],
              'outputs': {name: {'path': rel(args.output_dir/name), 'sha256': text_hash(content)}
                          for name, content in outputs.items()},
              'ordering': 'Machine IDs and per-ID source names are sorted lexicographically.'}
    if load_manifest(args.manifest)[3] != manifest_inputs or sha(args.campaign_report) != campaign['report_sha256']:
        raise ValueError('Final campaign changed before queue publication')
    for name, expected in {**verified, **helper_hashes}.items():
        if sha(ROOT/name) != expected:
            raise ValueError('Candidate source changed before queue publication')
    for name, content in outputs.items():
        fixed(args.output_dir/name, content, args.check)
    fixed(args.report, json.dumps(report, indent=2, sort_keys=True)+'\n', args.check)
    print(json.dumps(short, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
