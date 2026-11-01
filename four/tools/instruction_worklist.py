"""Make a contributor worklist from exact instruction inventories and evidence.

Claims organize work; only a recorded Coq proof inventory closes a family.
All generated tables and the standalone browser are disposable build outputs.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import re

from check_campaign import ROOT, packed, read_inventory, sha, unpack
from instruction_residual import residual

LANES = {
    'retry_history': 'Retry history timeouts',
    'refine_history': 'Refine rejected history certificates',
    'sparse_target': 'Prove sparse instruction returns',
    'frequent_target': 'Refine a frequently observed target',
    'exclude_target': 'Prove a target absent from the tail',
    'adapt_state_proof': 'Adapt an existing individual state proof',
    'needs_triage': 'No attached instruction diagnostic',
    'proved': 'Recorded instruction proof',
}
FIELDS = ['id', 'batch', 'machine', 'righthand_machine', 'proof_status', 'lane',
          'work_status', 'owner', 'missing_targets', 'search_history', 'state_case',
          'state_package', 'evidence', 'proof_theorem', 'note', 'pr']
WORK_STATES = {'unclaimed', 'in_progress', 'proposed'}


def identity(machine):
    """An injective ID for the exact table; no truncated hash or renaming."""
    return 'tr24-' + str(packed(machine))


def batch_id(machine):
    return f'b{packed(machine) % 256:02x}'


def righthand(machine):
    return machine.translate(str.maketrans('LR', 'RL')) if machine[1] == 'L' else machine


def load_rows():
    summary_path = ROOT / 'research/instruction-burndown-summary.json'
    summary = json.loads(summary_path.read_text())
    for name, expected in summary['inputs_sha256'].items():
        if sha(ROOT / name) != expected:
            raise ValueError('Recorded instruction accounting input differs: ' + name)
    baseline = ROOT / 'research/instruction-baseline.json'
    machines, pins = residual(baseline, summary['inputs_sha256'][str(baseline.relative_to(ROOT))])
    pins[str(summary_path.relative_to(ROOT))] = sha(summary_path)
    rows = {m: dict.fromkeys(FIELDS, '') for m in machines}
    for machine, row in rows.items():
        row.update(id=identity(machine), batch=batch_id(machine), machine=machine,
                   righthand_machine=righthand(machine), proof_status='open',
                   lane='needs_triage', work_status='unclaimed')
    for upgrade in summary['upgrades']:
        path = ROOT / 'research' / (upgrade['name'] + '-checked.json')
        report = json.loads(path.read_text())
        for machine in read_inventory(report['descriptor']['inventories'][0]):
            row = rows[machine]
            if row['proof_status'] != 'open':
                raise ValueError('Duplicate proof credit in worklist')
            row.update(proof_status='proved', lane='proved', proof_theorem=upgrade['theorem'],
                       evidence=str(path.relative_to(ROOT)))

    def evidence(name):
        path = ROOT / name
        pins[name] = sha(path)
        return json.loads(path.read_text())

    search = evidence('research/instruction-burn1-search.json')
    history = {}
    for stage in search['results']:
        for item in stage['rows']:
            history.setdefault(item['machine'], []).append(item['status'])
    for machine, statuses in history.items():
        row = rows[machine]
        row['search_history'] = ','.join(statuses)
        if row['proof_status'] == 'open':
            row['lane'] = 'retry_history' if all(s == 'timeout' for s in statuses) else 'refine_history'
            row['evidence'] = 'research/instruction-burn1-search.json'

    diagnostics = evidence('research/burn3-capacity-instruction-diagnostics.json')
    for entry in diagnostics['rows']:
        row = rows.get(entry['machine'])
        if row is None or row['proof_status'] != 'open':
            continue
        targets = entry['missing_any_witness']
        row['missing_targets'] = ','.join(f'{"AB"[t // 4]}{t % 4}' for t in targets)
        row['evidence'] = 'research/burn3-capacity-instruction-diagnostics.json'
        observed = [entry['targets'][str(t)] for t in targets]
        if all(t['category'] == 'last_observed_before_anchor' for t in observed):
            row['lane'] = 'exclude_target'
        elif all(t['category'] == 'observed_in_final_interval' and t['total_firings'] <= 1000 for t in observed):
            row['lane'] = 'sparse_target'
        else:
            row['lane'] = 'frequent_target'

    for name in ('state-case-proofs-checkpoint', 'state-case-proofs-additional', 'state-case-proofs-recent'):
        manifest = evidence('research/' + name + '.json')
        for package in manifest['packages']:
            for case in package['cases']:
                row = rows.get(case['machine'])
                if row is None:
                    continue
                row.update(state_case=case['id'], state_package=package['package'])
                if row['proof_status'] == 'open' and row['lane'] == 'needs_triage':
                    row['lane'] = 'adapt_state_proof'
                    row['evidence'] = package['report']
    final_case = evidence('research/burn43-s071-far-proof-input.json')
    for case in final_case['rows']:
        row = rows.get(case['machine'])
        if row is not None:
            row.update(state_case=f'S{final_case["frozen_checkpoint_index"] + 1:03d}',
                       state_package='burn43-s071-far')
            if row['proof_status'] == 'open' and row['lane'] == 'needs_triage':
                row.update(lane='adapt_state_proof', evidence='research/burn43-s071-far-checked.json')
    actual_open = {m for m, row in rows.items() if row['proof_status'] == 'open'}
    text = ''.join(m + '\n' for m in sorted(actual_open))
    if (len(actual_open) != summary['remaining_instruction_families'] or
            hashlib.sha256(text.encode()).hexdigest() != summary['remaining_machine_text_sha256']):
        raise ValueError('Worklist differs from the exact open inventory')
    return sorted(rows.values(), key=lambda row: int(row['id'][5:])), pins


def apply_claims(rows, claims):
    if claims.get('schema_version') != 1 or set(claims) != {'schema_version', 'batches', 'machines'}:
        raise ValueError('Unknown instruction claims schema')
    ids = {r['id'] for r in rows}
    batches = {r['batch'] for r in rows}
    for kind, allowed in (('machines', ids), ('batches', batches)):
        if not isinstance(claims[kind], dict) or set(claims[kind]) - allowed:
            raise ValueError('Unknown machine or batch claim')
        for claim in claims[kind].values():
            if (not isinstance(claim, dict) or set(claim) - {'owner', 'status', 'note', 'pr'} or
                    any(not isinstance(value, str) for value in claim.values()) or
                    claim.get('status', 'in_progress') not in WORK_STATES or
                    (claim.get('status', 'in_progress') != 'unclaimed' and not claim.get('owner', '').strip())):
                raise ValueError('Invalid claim; proof status can only change through an accepted proof inventory')
    for row in rows:
        claim = claims['machines'].get(row['id'], claims['batches'].get(row['batch'], {}))
        if claim:
            row.update(owner=claim.get('owner', ''), work_status=claim.get('status', 'in_progress'),
                       note=claim.get('note', ''), pr=claim.get('pr', ''))


def next_rows(rows, limit=64):
    order = {name: i for i, name in enumerate(LANES)}
    return sorted((r for r in rows if r['proof_status'] == 'open' and r['work_status'] == 'unclaimed'),
                  key=lambda r: (order[r['lane']], int(r['id'][5:])))[:limit]


def markdown(rows, title):
    lines = ['# ' + title, '', 'Only an accepted instruction proof inventory closes a family.', '',
             '| ID | Program (first move right) | Work lane | Missing targets | State case |',
             '| :-- | :-- | :-- | :-- | :-- |']
    for row in rows:
        lines.append(f'| `{row["id"]}` | `{row["righthand_machine"]}` | {LANES[row["lane"]]} | '
                     f'{row["missing_targets"] or "unknown"} | {row["state_case"] or "—"} |')
    return '\n'.join(lines) + '\n'


def export_tsv(rows):
    stream = io.StringIO()
    writer = csv.DictWriter(stream, FIELDS, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/instruction-worklist')
    parser.add_argument('--batch', help='Export one stable batch, b00 through bff')
    parser.add_argument('--machine', help='Show one stable tr24-N machine ID')
    parser.add_argument('--next-count', type=int, default=64)
    args = parser.parse_args()
    if not 1 <= args.next_count <= 1024:
        parser.error('Next batch must have 1 to 1024 families')
    rows, pins = load_rows()
    claims_path = ROOT / 'research/instruction-claims.json'
    apply_claims(rows, json.loads(claims_path.read_text()))
    pins[str(claims_path.relative_to(ROOT))] = sha(claims_path)
    opened = [r for r in rows if r['proof_status'] == 'open']
    summary = dict(scope='Historical hard-cohort work scheduling; no new proof credit.',
        open=len(opened), proved=len(rows)-len(opened),
        lanes=dict(Counter(r['lane'] for r in opened)),
        batches=dict(sorted(Counter(r['batch'] for r in opened).items())), inputs_sha256=pins)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'machines.tsv').write_text(export_tsv(opened))
    (args.output / 'all-families.tsv').write_text(export_tsv(rows))
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    (args.output / 'next64.md').write_text(markdown(next_rows(rows, args.next_count), 'Next instruction families'))
    from instruction_worklist_html import render
    (args.output / 'index.html').write_text(render(rows, summary, FIELDS, LANES))
    if args.batch:
        if not re.fullmatch(r'b[0-9a-f]{2}', args.batch):
            parser.error('Batch ID must be b00 through bff')
        selected = [r for r in opened if r['batch'] == args.batch]
        (args.output / (args.batch + '.md')).write_text(markdown(selected, 'Instruction batch ' + args.batch))
        (args.output / (args.batch + '.tsv')).write_text(export_tsv(selected))
    if args.machine:
        selected = [r for r in rows if r['id'] == args.machine]
        if not selected:
            parser.error('Unknown machine ID')
        print(json.dumps(selected[0], indent=2))
    print(json.dumps({k: summary[k] for k in ('open', 'proved', 'lanes')}, indent=2))
    print('Worklist: ' + str(args.output / 'index.html'))


if __name__ == '__main__':
    main()
