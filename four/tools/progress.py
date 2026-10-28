"""Combine audited proof outcomes for the fixed 1,024-family sample.

Run after check_affine_batch.py and make -C four check. The explicit evidence
registry pins the audited reports and pipeline proof sources. This script only
checks bookkeeping; it never promotes a search verdict to a proved bound.
The original burndown-sample.tsv remains the frozen search baseline.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import re

import burndown
import generate_pipeline_examples

ROOT = Path(__file__).resolve().parents[1]
FIELDS = ['machine', 'status', 'state_bound', 'instruction_bound', 'proof',
          'affine_status', 'pipeline_checked', 'census_proof', 'census_linked']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_rows(path):
    with path.open() as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    require(len(rows) == len({r['machine'] for r in rows}), f'Duplicate machine: {path}')
    return {r['machine']: r for r in rows}


def check_hashes(base, hashes):
    for relative, expected in hashes.items():
        require(sha(base/relative) == expected, f'Audited evidence changed: {relative}')


def load_evidence():
    registry = json.loads((ROOT/'research/progress-verified.json').read_text())
    check_hashes(ROOT, registry['input_sha256'])
    check_hashes(ROOT, registry['pipeline']['source_sha256'])
    baseline = read_rows(ROOT/'research/burndown-sample.tsv')
    baseline_summary = json.loads((ROOT/'research/burndown-summary.json').read_text())
    require(len(baseline) == baseline_summary['sample_size'] == 1024,
            'Progress must cover the frozen 1,024-family sample')
    require(Counter(r['status'] for r in baseline.values()) ==
            baseline_summary['sample_status_counts'], 'Baseline status counts changed')
    verified = json.loads((ROOT/'research/burndown-verified.json').read_text())
    burndown.validate_registry(verified)

    affine = read_rows(ROOT/'research/affine-batch.tsv')
    affine_summary = json.loads((ROOT/'research/affine-batch-summary.json').read_text())
    check_hashes(ROOT.parent, affine_summary['source_sha256'])
    require(sha(ROOT/'research/affine-batch-certs.json') == affine_summary['bundle_sha256'],
            'Affine certificate bundle changed')
    require(affine_summary['sample_sha256'] == baseline_summary['sample_sha256'],
            'Affine report belongs to another sample')
    candidates = {m for m, r in baseline.items()
                  if r['status'] in ('coq_checked', 'candidate_unchecked')}
    require(set(affine) == candidates, 'Affine report must cover exactly the baseline candidates')
    require(Counter(r['status'] for r in affine.values()) == affine_summary['counts'],
            'Affine status counts differ from audited report')
    bundle = json.loads((ROOT/'research/affine-batch-certs.json').read_text())
    require(set(bundle) == candidates, 'Affine bundle IDs differ from the candidate inventory')
    old_links = set(verified['census_closeout']['machines'])
    require(old_links <= {m for m, r in affine.items() if r['status'] == 'coq_checked'},
            'Existing census link lacks an accepted affine proof')
    for machine, row in affine.items():
        require(row['status'] in ('coq_checked', 'checker_rejected'), 'Unknown affine status')
        require(hashlib.sha256(bundle[machine].encode()).hexdigest() == row['certificate_sha256'],
                f'Affine certificate identity changed: {machine}')
        require(row['census_linked'] == ('yes' if machine in old_links else 'no'),
                f'Unexpected affine census link: {machine}')
        if row['status'] == 'coq_checked':
            require(row['state_bound'] == row['instruction_bound'] == '4096',
                    'Unexpected affine bounds')
            require(row['theorem'].endswith('.completions_' + machine.replace('-', 'X')),
                    f'Wrong affine completion theorem: {machine}')

    pipeline_data = json.loads((ROOT/'research/pipeline-examples.json').read_text())
    pipeline_rows = pipeline_data['rows']
    pipeline = {r['machine']: r for r in pipeline_rows}
    require(len(pipeline) == len(pipeline_rows) == registry['pipeline']['families'],
            'Pipeline family count changed or duplicated')
    require(set(pipeline) <= set(baseline), 'Pipeline contains a family outside this sample')
    require((ROOT/'theories/PipelineExamples.v').read_text() ==
            generate_pipeline_examples.generate(pipeline_data),
            'Pipeline input and audited proof source differ')
    source = (ROOT/'theories/PipelineExamples.v').read_text()
    for key in ('bounds_theorem', 'coverage_theorem', 'discharge_theorem', 'residual_predicate'):
        name = registry['pipeline'][key]
        require(name.startswith('BBB24.PipelineExamples.'), 'Unexpected pipeline proof namespace')
        require(re.search(r'\b(?:Theorem|Lemma|Definition)\s+' + re.escape(name.split('.')[-1])
                          + r'\b', source), f'Missing pipeline declaration: {name}')
    return registry, baseline, affine, pipeline, verified


def build():
    registry, baseline, affine, pipeline, verified = load_evidence()
    rows = []
    for machine in sorted(baseline):
        a = affine.get(machine)
        pipeline_checked = machine in pipeline
        affine_checked = a is not None and a['status'] == 'coq_checked'
        old_link = machine in verified['census_closeout']['machines']
        status = ('coq_checked' if pipeline_checked or affine_checked else
                  'checker_rejected' if a is not None else 'no_certificate')
        proof = (registry['pipeline']['bounds_theorem'] if pipeline_checked else
                 a['theorem'] if affine_checked else '')
        census_proof = (registry['pipeline']['discharge_theorem'] if pipeline_checked else
                        verified['census_closeout']['discharge_theorem'] if old_link else '')
        rows.append(dict(machine=machine, status=status,
                         state_bound=4096 if status == 'coq_checked' else '',
                         instruction_bound=4096 if status == 'coq_checked' else '', proof=proof,
                         affine_status=a['status'] if a is not None else 'not_candidate',
                         pipeline_checked='yes' if pipeline_checked else 'no',
                         census_proof=census_proof, census_linked='yes' if census_proof else 'no'))
    accepted = {m for m, r in affine.items() if r['status'] == 'coq_checked'}
    summary = dict(
        scope='Current proof outcomes for the frozen 1,024-family sample only; not a full-queue remainder.',
        families=len(rows), status_counts=dict(sorted(Counter(r['status'] for r in rows).items())),
        affine_checked=len(accepted), pipeline_checked=len(pipeline),
        checked_by_both=len(accepted & set(pipeline)),
        additional_pipeline_checked=len(set(pipeline) - accepted),
        census_linked=sum(r['census_linked'] == 'yes' for r in rows),
        census_residual_predicate=registry['pipeline']['residual_predicate'],
        census_coverage_theorem=registry['pipeline']['coverage_theorem'],
        census_accounting='Counts listed families, not removed whole census leaves or raw tables; original structural counts unchanged.',
        rejection_meaning='checker_rejected means this affine certificate invocation failed, not that the machine violates a bound.',
        evidence_registry_sha256=sha(ROOT/'research/progress-verified.json'),
        input_sha256=registry['input_sha256'])
    out = io.StringIO()
    writer = csv.DictWriter(out, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader(); writer.writerows(rows)
    return {'progress-sample.tsv': out.getvalue(),
            'progress-summary.json': json.dumps(summary, indent=2)+'\n'}, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs, summary = build()
    for name, contents in outputs.items():
        path = ROOT/'research'/name
        if args.check:
            require(path.read_text() == contents, f'{name} is stale')
        else:
            path.write_text(contents)
    print(json.dumps({'status_counts': summary['status_counts'],
                      'census_linked': summary['census_linked']}, sort_keys=True))


if __name__ == '__main__':
    main()
