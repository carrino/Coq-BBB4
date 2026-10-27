"""Verify the frozen campaign and its supplement, then report their exact union.

This is census-family accounting, not a new global upper-bound proof. Both
inputs must have current successful complete-closure kernel audit receipts.
Historical reports remain unchanged; local receipt identities are not included
in the portable summary. The remaining candidate queue is scheduling only.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path

from check_campaign import ROOT, CHAMPION, ledger, load_manifest, read_inventory, sha
from check_campaign_next import load_manifest as load_supplement
from kernel_audit_cache_v3 import ReceiptValidation, _runtime
from summarize_campaign_queue import fixed, machine_text, verify_campaign


def table(rows, fields):
    out = io.StringIO()
    writer = csv.DictWriter(out, fields, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-manifest', type=Path,
                        default=ROOT/'research/campaign-final-input.json')
    parser.add_argument('--baseline-report', type=Path,
                        default=ROOT/'research/campaign-final-summary.json')
    parser.add_argument('--supplement-manifest', type=Path,
                        default=ROOT/'research/next-campaign-input.json')
    parser.add_argument('--supplement-report', type=Path,
                        default=ROOT/'research/next-campaign-summary.json')
    parser.add_argument('--queue-report', type=Path,
                        default=ROOT/'research/campaign-next-summary.json')
    parser.add_argument('--report', type=Path,
                        default=ROOT/'research/next-burndown-summary.json')
    parser.add_argument('--output-dir', type=Path,
                        default=ROOT/'build/next-burndown')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    validation = ReceiptValidation()
    runtime = _runtime()
    protected = {}
    proof_inputs = []

    def pin(path, expected):
        path = path.resolve()
        previous = protected.setdefault(path, expected)
        if previous != expected:
            raise ValueError('Conflicting pinned artifact: '+str(path))

    def campaign(manifest_path, report_path, loader):
        manifest, boards, _, inputs = loader(manifest_path)
        cohort = set(read_inventory(manifest['cohort']))
        checked, texts = {}, {}
        for scope in ('both', 'state'):
            families, texts[scope] = ledger(boards, scope)
            checked[scope] = set(families)
        metadata = verify_campaign(report_path, manifest, boards, inputs,
                                   cohort, checked, texts)
        report = json.loads(report_path.read_text())
        pin(report_path, metadata['report_sha256'])
        for group in ('inputs', 'source_sha256'):
            for name, expected in report[group].items():
                pin(ROOT/name, expected)
        local = (ROOT/report['ledgers']['both']['path']).parent/'latest-audit.json'
        pin(local, sha(local))
        actual = json.loads(local.read_text())
        for phase in [actual, *actual.get('phases', [])]:
            path = ROOT/phase['receipt']
            pin(path, phase['receipt_sha256'])
            receipt = validation.load(path)
            snapshot = receipt['snapshot']
            if snapshot['runtime'] != runtime:
                raise ValueError('Current Coq runtime differs from local audit; replay first')
            for item in snapshot['graph'].values():
                pin(Path(item['source']), item['source_sha256'])
                pin(Path(item['object']), item['object_sha256'])
            for name, expected in snapshot['plugins'].items():
                pin(Path(name), expected)
        if report['module'] not in validation.load(ROOT/actual['receipt'])['roots']:
            raise ValueError('Audit does not cover the reported campaign root')
        proof_inputs.append({**metadata, 'manifest': str(manifest_path.resolve().relative_to(ROOT)),
                             'manifest_sha256': sha(manifest_path)})
        return boards, cohort, checked

    baseline, cohort, old = campaign(args.baseline_manifest, args.baseline_report, load_manifest)
    supplement, new_cohort, new = campaign(args.supplement_manifest, args.supplement_report,
                                          load_supplement)
    if new_cohort != cohort:
        raise ValueError('Supplement comparison cohort differs')
    if len({b['id'] for b in baseline+supplement}) != len(baseline+supplement):
        raise ValueError('Repeated board ID across campaigns')
    combined, contents, counts = {}, {}, {}
    for scope in ('both', 'state'):
        families, text = ledger(baseline+supplement, scope)
        combined[scope] = set(families)
        if combined[scope] != old[scope] | new[scope]:
            raise ValueError('Ledger union differs')
        residual = cohort-combined[scope]
        delta = (new[scope]-old[scope]) & cohort
        contents[scope+'-families.tsv'] = text
        contents[scope+'-remaining.txt'] = machine_text(residual)
        contents[scope+'-newly-covered.txt'] = machine_text(delta)
        counts[scope] = {'distinct_families': len(combined[scope]),
                         'cohort_covered': len(cohort & combined[scope]),
                         'cohort_remaining': len(residual),
                         'newly_covered_cohort': len(delta)}
    if not combined['both'] <= combined['state']:
        raise ValueError('Both-bound families missing from state coverage')
    if CHAMPION not in combined['both'] or CHAMPION not in combined['state']:
        raise ValueError('Expected the independently checked champion registration')

    queue = json.loads(args.queue_report.read_text())
    pin(args.queue_report, sha(args.queue_report))
    if queue['campaign']['report_sha256'] != proof_inputs[0]['report_sha256']:
        raise ValueError('Candidate queue belongs to another baseline')
    queue_path = ROOT/queue['outputs']['queued.tsv']['path']
    pin(queue_path, queue['outputs']['queued.tsv']['sha256'])
    with queue_path.open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    if len(rows) != queue['totals']['unique_queued_machine_rows'] or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Candidate queue count differs')
    remaining = []
    for row in rows:
        machine = row['machine']
        both = row['both_sources'] if machine not in combined['both'] else ''
        state = row['state_sources'] if machine not in combined['state'] else ''
        if both or state:
            remaining.append({'machine': machine,
                              'state_already_checked': 'yes' if machine in combined['state'] else 'no',
                              'both_sources': both, 'state_sources': state})
    remaining.sort(key=lambda row: row['machine'])
    fields = ['machine', 'state_already_checked', 'both_sources', 'state_sources']
    contents['queued.tsv'] = table(remaining, fields)
    for scope in ('both', 'state'):
        contents[scope+'-queued.txt'] = machine_text(row['machine'] for row in remaining
                                                    if row[scope+'_sources'])
    helper_paths = [Path(__file__), ROOT/'tools/check_campaign.py',
                    ROOT/'tools/check_campaign_next.py', ROOT/'tools/campaign_next_boards.py',
                    ROOT/'tools/kernel_audit_cache_v3.py', ROOT/'tools/summarize_campaign_queue.py']
    helpers = {str(path.resolve().relative_to(ROOT)): sha(path) for path in helper_paths}
    for path in helper_paths:
        pin(path, helpers[str(path.resolve().relative_to(ROOT))])
    validation.recheck()
    for path, expected in protected.items():
        if sha(path) != expected:
            raise ValueError('Audited input, source, object or receipt changed: '+str(path))
    outputs = {name: {'path': str((args.output_dir/name).resolve().relative_to(ROOT)),
                      'sha256': hashlib.sha256(text.encode()).hexdigest()}
               for name, text in contents.items()}
    report = {'scope': 'Distinct census families from independently audited exact boards; all completions covered. No subtraction of raw census table weights.',
              'proof_inputs': proof_inputs, 'cohort_rows': len(cohort),
              'baseline_boards': len(baseline), 'supplement_boards': len(supplement),
              'counts': counts, 'champion_registered': True,
              'global_upper_bound_proved': False,
              'remaining_candidate_queue': {
                  'scope': 'Scheduling only; remaining candidates are not proof successes.',
                  'both': sum(bool(row['both_sources']) for row in remaining),
                  'state': sum(bool(row['state_sources']) for row in remaining),
                  'distinct': len(remaining),
                  'original_queue_report': str(args.queue_report.resolve().relative_to(ROOT)),
                  'original_queue_report_sha256': sha(args.queue_report)},
              'outputs': outputs, 'helper_sha256': helpers}
    for name, text in contents.items():
        fixed(args.output_dir/name, text, args.check)
    fixed(args.report, json.dumps(report, indent=2, sort_keys=True)+'\n', args.check)
    print(json.dumps({'counts': counts, 'remaining_candidates': report['remaining_candidate_queue']},
                     indent=2))


if __name__ == '__main__':
    main()
