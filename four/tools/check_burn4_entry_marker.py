"""Replay the frozen entry-marker theorem, regressions and exact 121-row census board.

Copies frozen handwritten sources into an isolated build namespace, generates
an exact all-completion state-zero board and inventory wrapper, and audits the
complete dependency closure. Published evidence is immutable.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
from generate_pipeline_examples import codes
import kernel_audit_cache_v3

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn4-entry-marker/proof'
NAMESPACE = 'BBB24Burn4EntryMarker'
PREFIX = ROOT / 'research/burn4-entry-marker'
TEMPLATES = ['EntryMarker.v', 'EntryRegression.v']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(contents)


def batch_source(rows):
    packed = ';\n'.join('  mkMPRow ' + str(row['code']) + '%N ' + str(row['marker_mask'])
                       + '%N ' + ' '.join(str(w) + '%N' for w in row['weights'][1:]) for row in rows)
    return r'''(** Generated exact state-only entry-marker batch. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout StateOnlyCloseout
  StatePipeline MarkerPotential.
From BBB24Burn4EntryMarker Require Import EntryMarker EntryRegression.
Import ListNotations.
Definition rows : list MPRow := [
''' + packed + r'''
].
Definition row_check row := em_check(stp_machine(mp_code row))(mp_mask row)
 (N.to_nat(mp_w1 row))(N.to_nat(mp_w2 row))(N.to_nat(mp_w3 row)).
Lemma checked : forallb row_check rows=true.
Proof. vm_compute;reflexivity. Qed.
Definition board := mp_board rows.
Theorem small_sound : StateBoardSound 0 board.
Proof.
 intros family Hin tm Hle. unfold board,mp_board in Hin.
 apply in_map_iff in Hin as(row&<-&Hin).
 pose proof checked as H. apply forallb_forall with(x:=row)in H;[|exact Hin].
 unfold row_check in H.
 destruct(em_check_sound _ _ _ _ _ H)as[Hnh Hb].
 eapply state_bound_extend;eauto.
Qed.
Theorem sound : StateBoardSound score board.
Proof. apply state_board_zero_weaken;exact small_sound. Qed.
Lemma pending_checked : forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem was_pending : forall family,In family board -> bootstrap_pending family.
Proof.
 intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
 apply forallb_forall with(x:=family)in H;assumption.
Qed.
Print Assumptions small_sound.
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        parser.error('Replay budgets must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = artifact('input.json')
    report_path, inventory_path = artifact('checked.json'), artifact('machines.json')
    protected = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    data = json.loads(input_path.read_text())
    source_report = ROOT / data['source_report']
    if sha(source_report) != data['source_report_sha256']:
        raise ValueError('Frozen candidate report differs')
    search = json.loads(source_report.read_text())
    rows = data['rows']
    machines = [row['machine'] for row in rows]
    if rows != search['rows'] or len(rows) != 121 or len(set(machines)) != 121 or data['state_bound'] != 0:
        raise ValueError('Expected exactly121 selected state-zero witnesses')
    residual = ROOT / data['residual_input']
    residual_ids = residual.read_text().splitlines()
    if sha(residual) != data['residual_sha256'] or len(residual_ids) != 667 or not set(machines) <= set(residual_ids):
        raise ValueError('Expected candidates inside the frozen 667 residual')
    for row in rows:
        if sum(v * 17**i for i, v in enumerate(codes(row['machine']))) != row['code']:
            raise ValueError('Packed machine code differs')
        if (type(row['marker_mask']) is not int or not 0 <= row['marker_mask'] < 16
            or len(row['weights']) != 4 or row['weights'][0] != 0
            or any(type(w) is not int or not 0 <= w <= 4 for w in row['weights'])):
            raise ValueError('Invalid finite marker witness')
    templates = [ROOT / 'proof-sources/burn4-entry-marker' / name for name in TEMPLATES]
    template_pins = {str(p.relative_to(ROOT)): sha(p) for p in templates}
    if template_pins != data['template_sha256']:
        raise ValueError('Frozen handwritten proof template differs')
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in (input_path, source_report, residual)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [part for directory, namespace in load_paths for part in ('-Q', str(directory), namespace)]
    paths = []
    for template in templates:
        path = OUTPUT / template.name
        exact(path, template.read_text())
        paths.append(path)
    path = OUTPUT / 'Batch.v'
    exact(path, batch_source(rows))
    paths.append(path)
    descriptor = {'id': 'burn4_entry_marker', 'scope': 'state', 'rows': 121,
        'state_bound': 0, 'instruction_bound': None, 'module': NAMESPACE + '.Inventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NAMESPACE + '.Batch', 'machines': machines}))
    paths.append(path)
    sources = dependency_hashes(paths, flags)
    for name in ('check_burn4_entry_marker.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps({'rows': [{'machine': machine} for machine in machines]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'template_sha256': template_pins, 'source_sha256': sources,
              'descriptor': descriptor, 'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': 121, 'checked_instruction_families': 0}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen replay evidence differs')
    if previous and (not inventory_path.exists() or sha(inventory_path) != stable['inventory_sha256']):
        raise ValueError('Frozen inventory differs')
    timings = {}
    for path in paths:
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - start, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache_v3.fresh_paths(OUTPUT, 'kernel-audit')
    start = time.monotonic()
    audit = kernel_audit_cache_v3.audit([NAMESPACE + '.Inventory'], [paths[-1]], load_paths,
                                      receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **template_pins, **sources}.items()):
        raise ValueError('Pinned input, template or dependency changed during replay')
    if any(sha(path) != digest for path, digest in protected.items()):
        raise ValueError('Published report or inventory changed during replay')
    current = {**stable, 'scope': 'Exact state-only census bound0; all completions covered. No instruction claim.',
               'compile_seconds': timings, 'kernel_receipt': str(receipt.relative_to(ROOT)),
               'kernel_receipt_sha256': sha(receipt), 'kernel_audit': 'Full recursive coqchk.',
               'audit_seconds': round(time.monotonic() - start, 3),
               'checked_modules': len(audit['checked_modules']), 'reused_modules': len(audit['reused_modules']),
               'object_sha256': {str(path.with_suffix('.vo').relative_to(ROOT)):
                                sha(path.with_suffix('.vo')) for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('121 entry-marker state families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
