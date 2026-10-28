"""Combine census boards while keeping state-only and both-bound claims separate.

The inventory of every imported board is itself checked in Coq. Counts therefore
come from the same tables as the proof, rather than trusting a search ledger or
an earlier report's label. Generated proof files and large ledgers stay in build/.
The final aggregate always receives a full recursive coqchk audit.
"""
import argparse
import base64
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import time
import zlib

from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
CHAMPION = '1LB2RA1LA1RB_0RB2LB3LB1RA'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependency_hashes(roots, flags):
    """Pin both local libraries, including the completed SmallBB theorem."""
    seen, pending = set(), {path.resolve() for path in roots}
    while pending:
        batch = sorted(pending-seen)
        if not batch:
            break
        seen.update(batch)
        output = subprocess.check_output(['coqdep', *flags, *map(str, batch)],
                                         cwd=ROOT.parent, text=True)
        pending = set()
        for line in output.splitlines():
            if ': ' not in line or not line.split()[0].endswith('.vo'):
                continue
            for token in line.split(': ', 1)[1].split():
                if token.endswith('.vo'):
                    path = Path(token).with_suffix('.v')
                    path = (path if path.is_absolute() else ROOT.parent/path).resolve()
                    path.relative_to(ROOT.parent)
                    if not path.is_file():
                        raise ValueError(f'Missing proof dependency: {path}')
                    pending.add(path)
    return {os.path.relpath(path, ROOT): sha(path) for path in sorted(seen)}


def unpack(value, radix):
    if type(value) is not int or not 0 <= value < radix**8:
        raise ValueError('Invalid packed machine')
    cells = []
    for _ in range(8):
        value, cell = divmod(value, radix)
        cells.append('---' if cell == 16 else
                     f'{cell//4}{"R" if cell&2 else "L"}{"B" if cell&1 else "A"}')
    return ''.join(cells[:4]) + '_' + ''.join(cells[4:])


def packed(machine):
    return sum(cell * 17**i for i, cell in enumerate(codes(machine)))


def read_inventory(spec):
    path = ROOT/spec['path']
    data = json.loads(path.read_text())
    if data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compressed inventory hash mismatch')
        data = json.loads(raw)
    fmt = spec['format']
    if fmt == 'columns':
        rows = [row[0] for row in data['rows']]
    elif fmt == 'rows':
        rows = [row['machine'] for row in data['rows']]
    elif fmt in ('packed16', 'packed17'):
        rows = [unpack(row, int(fmt[6:])) for row in data['rows']]
    elif fmt == 'packed17_groups':
        rows = [unpack(row, 17) for group in data['groups'] for row in group['rows']]
    elif fmt == 'transport':
        rows = [row[0] for key in ('images', 'shadow_images') for row in data[key]]
    elif fmt == 'affine':
        rows = list(data['certificates'])
    else:
        raise ValueError(f'Unknown inventory encoding: {fmt}')
    for machine in rows:
        codes(machine)
    order = spec.get('order', 'input')
    if order == 'sha256':
        rows.sort(key=lambda machine: hashlib.sha256(machine.encode()).digest())
    elif order == 'machine':
        rows.sort()
    elif order != 'input':
        raise ValueError('Unknown inventory ordering')
    if not rows:
        raise ValueError('Empty board inventory')
    return rows


def load_manifest(path):
    path = path.resolve()
    manifest = json.loads(path.read_text())
    boards = manifest['boards']
    if not boards or len({board['id'] for board in boards}) != len(boards):
        raise ValueError('Empty or repeated board IDs')
    paths = {'theories': 'BBB24'}
    inputs = {str(path.relative_to(ROOT)): sha(path), 'tools/check_campaign.py': sha(Path(__file__))}
    if 'cohort' in manifest:
        cohort = manifest['cohort']
        machines = read_inventory(cohort)
        if len(machines) != cohort['rows'] or len(set(machines)) != len(machines):
            raise ValueError('Incomplete or repeated comparison cohort')
        if hashlib.sha256(''.join(machine+'\n' for machine in machines).encode()).hexdigest() != cohort['machine_text_sha256']:
            raise ValueError('Comparison cohort differs from the frozen search remainder')
        if CHAMPION not in machines:
            raise ValueError('Comparison cohort lost its champion control')
        inputs[cohort['path']] = sha(ROOT/cohort['path'])
    for board in boards:
        for field in ('id', 'module', 'board', 'sound', 'small_sound', 'was_pending'):
            if not IDENT.fullmatch(board[field]):
                raise ValueError(f'Invalid Coq name: {field}')
        if board['scope'] not in ('both', 'state'):
            raise ValueError('A board must explicitly declare both or state scope')
        for field in ('state_bound', 'instruction_bound'):
            value = board.get(field)
            if field == 'instruction_bound' and board['scope'] == 'state':
                if value is not None:
                    raise ValueError('A state-only board cannot claim an instruction bound')
            elif type(value) is not int or value < 0:
                raise ValueError('Missing or invalid proved bound')
        for item in board['load_paths']:
            if not IDENT.fullmatch(item['namespace']):
                raise ValueError('Invalid namespace')
            previous = paths.setdefault(item['path'], item['namespace'])
            if previous != item['namespace']:
                raise ValueError('Conflicting logical paths')
        board['machines'] = [machine for spec in board['inventories'] for machine in read_inventory(spec)]
        for spec in board['inventories']:
            inputs[spec['path']] = sha(ROOT/spec['path'])
        if len(board['machines']) != board['rows']:
            raise ValueError(f"Inventory size changed for {board['id']}")
        if CHAMPION in board['machines']:
            raise ValueError('Small-bound board unexpectedly includes the champion')
    if not any(board['scope'] == 'both' for board in boards):
        raise ValueError('Need at least one both-bound board')
    if not any(board['scope'] == 'state' for board in boards):
        raise ValueError('Need at least one state-only board')
    return manifest, boards, paths, inputs


HEADER = '''(** GENERATED by four/tools/check_campaign.py. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard CensusUnion StateOnlyCloseout DualCloseout OrbitCloseout BoardManifest.
Import ListNotations.
'''


def inventory_source(board):
    module = board['module']
    numbers = [f'{packed(machine)}%N' for machine in board['machines']]
    chunks = []
    definitions = []
    for offset in range(0, len(numbers), 512):
        name = f'rows{len(chunks):04}'
        batch = numbers[offset:offset+512]
        body = ';\n  '.join(';'.join(batch[i:i+16]) for i in range(0, len(batch), 16))
        definitions.append(f'Definition {name} : list N := [\n  {body}].')
        chunks.append(name)
    rows = '\n'.join(definitions) + '\nDefinition rows := concat [' + ';'.join(chunks) + '].'
    bs = board['state_bound']
    if board['scope'] == 'both':
        small = f'BoardSound {bs}%N {board["instruction_bound"]}%N board'
        sound = 'BoardSound scoreN scoreN board'
    else:
        small = f'StateBoardSound (N.to_nat {bs}%N) board'
        sound = 'StateBoardSound score board'
    return HEADER + f'''Require Import {module}.
{rows}
Definition board := {module}.{board['board']}.
Lemma inventory_checked : manifest_check rows board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_exact : manifest_board rows = board.
Proof. apply manifest_check_sound. exact inventory_checked. Qed.
Theorem small_sound : {small}.
Proof. exact {module}.{board['small_sound']}. Qed.
Theorem sound : {sound}.
Proof. exact {module}.{board['sound']}. Qed.
Theorem was_pending : forall family, In family board -> bootstrap_pending family.
Proof. exact {module}.{board['was_pending']}. Qed.
'''


def forall_proof(modules, field):
    return '\n'.join(f'  apply Forall_cons; [exact {module}.{field}|].' for module in modules) + '\n  apply Forall_nil.'


def aggregate_source(namespace, boards):
    both = [board['id'] for board in boards if board['scope'] == 'both']
    state = [board['id'] for board in boards if board['scope'] == 'state']
    return HEADER + f'''From {namespace} Require Import {' '.join(board['id'] for board in boards)}.
Definition both_boards : list (list TM) := [{'; '.join(module+'.board' for module in both)}].
Definition state_only_boards : list (list TM) := [{'; '.join(module+'.board' for module in state)}].
Definition both_board := concat both_boards.
Definition state_only_board := concat state_only_boards.
Lemma both_sound : BoardSound scoreN scoreN both_board.
Proof. apply boards_sound. unfold both_boards.
{forall_proof(both, 'sound')}
Qed.
Lemma state_only_sound : StateBoardSound score state_only_board.
Proof. apply state_boards_sound. unfold state_only_boards.
{forall_proof(state, 'sound')}
Qed.
Lemma both_was_pending : forall family, In family both_board -> bootstrap_pending family.
Proof. apply boards_pending. unfold both_boards.
{forall_proof(both, 'was_pending')}
Qed.
Lemma state_only_was_pending : forall family, In family state_only_board -> bootstrap_pending family.
Proof. apply boards_pending. unfold state_only_boards.
{forall_proof(state, 'was_pending')}
Qed.
Definition state_board := both_board ++ state_only_board.
Lemma state_sound : StateBoardSound score state_board.
Proof. apply state_board_app; [apply bounds_board_state; exact both_sound|exact state_only_sound]. Qed.
Definition both_pending := remaining bootstrap_pending both_board.
Definition state_pending := remaining bootstrap_pending state_board.
Theorem both_coverage : forall tm, Bounds scoreN scoreN tm \\/ both_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage both_sound). Qed.
Theorem state_coverage : forall tm, QHBound score tm \\/ state_pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage state_sound). Qed.
Theorem both_families_discharged : forall family, In family both_board ->
  forall tm, TM_le family tm -> bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~both_pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ both_was_pending both_sound). Qed.
Lemma state_was_pending : forall family, In family state_board -> bootstrap_pending family.
Proof. apply pending_board_app; [exact both_was_pending|exact state_only_was_pending]. Qed.
Theorem state_families_discharged : forall family, In family state_board ->
  forall tm, TM_le family tm -> bootstrap_pending tm /\\ QHBound score tm /\\ ~state_pending tm.
Proof. exact (state_board_discharge _ _ state_was_pending state_sound). Qed.
Theorem state_pending_subset : forall tm, state_pending tm -> both_pending tm.
Proof. exact (dual_state_pending_subset both_board state_only_board). Qed.
Definition both_orbit_pending := orbit_remaining bootstrap_pending both_board.
Definition state_orbit_pending := orbit_remaining bootstrap_pending state_board.
Theorem both_orbit_coverage : forall tm, Bounds scoreN scoreN tm \\/ both_orbit_pending tm.
Proof. exact (orbit_closeout_coverage _ _ _ _ bootstrap_coverage both_sound). Qed.
Theorem state_orbit_coverage : forall tm, QHBound score tm \\/ state_orbit_pending tm.
Proof. exact (orbit_state_coverage _ _ _ bootstrap_state_coverage state_sound). Qed.
Print Assumptions both_coverage.
Print Assumptions state_coverage.
Print Assumptions both_families_discharged.
Print Assumptions state_families_discharged.
'''


def ledger(boards, scope):
    families = {}
    for board in boards:
        if scope == 'both' and board['scope'] != 'both':
            continue
        for machine in board['machines']:
            row = families.setdefault(machine, {'machine': machine, 'methods': [], 'state_bound': board['state_bound'],
                                                'instruction_bound': board['instruction_bound'] if scope == 'both' else '',
                                                'census_linked': 'yes'})
            row['methods'].append(board['id'])
            row['state_bound'] = min(row['state_bound'], board['state_bound'])
            if scope == 'both':
                row['instruction_bound'] = min(row['instruction_bound'], board['instruction_bound'])
    stream = io.StringIO()
    writer = csv.DictWriter(stream, ['machine', 'methods', 'state_bound', 'instruction_bound', 'census_linked'],
                            delimiter='\t', lineterminator='\n')
    writer.writeheader()
    for machine in sorted(families):
        row = dict(families[machine]); row['methods'] = ','.join(sorted(set(row['methods'])))
        writer.writerow(row)
    return families, stream.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'research/campaign-input.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/campaign-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/campaign')
    parser.add_argument('--namespace', default='BBB24Campaign')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--compile-only', action='store_true', help='Diagnostic only: no audit, report or ledger publication')
    parser.add_argument('--timeout', type=int, default=14400)
    args = parser.parse_args()
    for field in ('manifest', 'report', 'output_dir'):
        setattr(args, field, getattr(args, field).resolve())
    if not IDENT.fullmatch(args.namespace):
        raise ValueError('Invalid campaign namespace')
    manifest, boards, paths, inputs = load_manifest(args.manifest)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    paths[str(args.output_dir.resolve().relative_to(ROOT))] = args.namespace
    flags = [part for path, namespace in paths.items() for part in ('-Q', str(ROOT/path), namespace)]
    generated = []
    for board in boards:
        path = args.output_dir/(board['id']+'.v')
        path.write_text(inventory_source(board)); generated.append(path)
    aggregate = args.output_dir/'Campaign.v'
    aggregate.write_text(aggregate_source(args.namespace, boards)); generated.append(aggregate)
    dependencies = dependency_hashes(generated, flags)
    compiler = subprocess.check_output(['coqc', '--version'], text=True)
    evidence = {'inputs': inputs, 'source_sha256': dependencies, 'coq_version': compiler}
    if not args.refresh and not args.compile_only:
        old = json.loads(args.report.read_text())
        if any(old[key] != value for key, value in evidence.items()):
            raise ValueError('Campaign proof inputs changed; a fresh audit is required')
    for path in generated:
        receipt = path.with_suffix('.checked.json'); vo = path.with_suffix('.vo')
        current = {'source': sha(path), 'dependencies': dependency_hashes([path], flags), 'coq_version': compiler}
        if args.resume and receipt.exists() and vo.exists():
            prior = json.loads(receipt.read_text())
            if all(prior.get(key) == value for key, value in current.items()) and prior.get('vo_sha256') == sha(vo):
                print(f'Reused {path.stem}', flush=True); continue
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as stream:
            subprocess.run(['coqc', '-native-compiler', 'no', *flags, str(path)], cwd=ROOT.parent,
                           stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        receipt.write_text(json.dumps({**current, 'vo_sha256': sha(vo)}, indent=2)+'\n')
        print(f'Checked inventory {path.stem}: {time.monotonic()-start:.2f}s', flush=True)
    if args.compile_only:
        print('Compilation only; no audited report or ledger published.', flush=True)
        return
    with (args.output_dir/'coqchk.log').open('w') as stream:
        subprocess.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags, args.namespace+'.Campaign'],
                       cwd=ROOT.parent, stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
    if dependencies != dependency_hashes(generated, flags):
        raise ValueError('Proof dependencies changed during the recursive audit')
    if inputs != load_manifest(args.manifest)[3]:
        raise ValueError('Campaign inventory changed during the recursive audit')
    counts = {}
    ledgers = {}
    cohort_counts = {}
    cohort = set(read_inventory(manifest['cohort'])) if 'cohort' in manifest else None
    for scope in ('both', 'state'):
        families, contents = ledger(boards, scope)
        counts[scope] = len(families)
        path = args.output_dir/(scope+'-families.tsv')
        path.write_text(contents)
        ledgers[scope] = {'path': str(path.relative_to(ROOT)), 'sha256': sha(path)}
        if cohort is not None:
            unresolved = sorted(cohort-families.keys())
            path = args.output_dir/(scope+'-unproved-initial-cohort.txt')
            path.write_text(''.join(machine+'\n' for machine in unresolved))
            cohort_counts[scope] = {'cohort_rows': len(cohort), 'proved': len(cohort & families.keys()),
                                    'unproved': len(unresolved), 'unproved_path': str(path.relative_to(ROOT)),
                                    'unproved_sha256': sha(path)}
    report = {**evidence, 'scope': 'Distinct family IDs, with all completions covered; no raw-table weight subtraction.',
              'both_census_linked_families': counts['both'], 'state_census_linked_families': counts['state'],
              'initial_search_cohort': cohort_counts,
              'source_rows': {board['id']: len(board['machines']) for board in boards}, 'ledgers': ledgers,
              'module': args.namespace+'.Campaign', 'validation': 'Exact inventory VM proofs, typed bounds, pending membership, and full recursive coqchk.',
              'original_structural_weights_unchanged': True, 'global_upper_bound_proved': False}
    text = json.dumps(report, indent=2, sort_keys=True)+'\n'
    if args.refresh:
        args.report.write_text(text)
    elif args.report.read_text() != text:
        raise ValueError('Campaign report differs from checked evidence')
    print(json.dumps(counts), flush=True)


if __name__ == '__main__':
    main()
