"""Rebuild the frozen legacy weighted closeout with a fresh kernel audit.

Historical source and inventory bytes remain exact. Compiled objects are
validated by recursive coqchk, with their current hashes recorded locally;
the historical report and its machine inventory are never rewritten.
"""
import argparse
import json
from pathlib import Path
import re

import check_weighted as legacy
import check_weighted_closeout as closeout
from generate_pipeline_examples import codes
from replay_portable_weighted import run, serialized, sha, write_exact

ROOT = Path(__file__).resolve().parents[1]


def inventory_source(namespace, names):
    rows = [sum(value * 17**index for index, value in enumerate(codes(machine)))
            for machine in names]
    return '''From Coq Require Import List NArith.
From BBB24 Require Import BoardManifest.
From '''+namespace+''' Require Import WeightedCloseout.
Import ListNotations.
Definition frozen_rows : list N := ['''+';'.join(str(row)+'%N' for row in rows)+'''].
Lemma inventory_checked : manifest_check frozen_rows weighted_board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_exact : manifest_board frozen_rows = weighted_board.
Proof. apply manifest_check_sound. exact inventory_checked. Qed.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--weighted-report', type=Path, required=True)
    parser.add_argument('--proof-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=3600)
    args = parser.parse_args()
    if args.timeout < 1:
        raise ValueError('Positive timeout required')
    source_report_hash, report_hash = sha(args.weighted_report), sha(args.report)
    source = json.loads(args.weighted_report.read_text())
    report = json.loads(args.report.read_text())
    manifest = source['manifest']
    namespace = manifest['namespace']
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*', namespace):
        raise ValueError('Invalid source namespace')
    if manifest['state_bound'] != 4096 or manifest['instruction_bound'] != 4096:
        raise ValueError('Expected both source bounds at 4096')
    if legacy.source_hashes() != manifest['source_sha256']:
        raise ValueError('Frozen weighted checker sources differ')
    expected_inputs = {
        'source_report_sha256': source_report_hash,
        'wrapper_tool_sha256': sha(Path(closeout.__file__)),
        'bootstrap_sha256': sha(ROOT/'theories/Bootstrap.v'),
        'closeout_sha256': sha(ROOT/'theories/Closeout.v'),
        'certified_board_sha256': sha(ROOT/'theories/CertifiedBoard.v')}
    if report['inputs'] != expected_inputs:
        raise ValueError('Frozen closeout inputs differ')
    actual = {}
    for name, digest in source['artifacts_sha256'].items():
        path = args.proof_dir/name
        actual[name] = sha(path)
        if not name.endswith('.vo') and actual[name] != digest:
            raise ValueError('Source proof text differs: '+name)
    rows = [r for r in source['results'] if r['status'] == 'coq_checked']
    names = [r['machine'] for r in rows]
    if len(set(names)) != len(names) or report['families_discharged'] != len(names):
        raise ValueError('Frozen family inventory differs')
    if (args.proof_dir/'machines.txt').read_text() != ''.join(m+'\n' for m in names):
        raise ValueError('Source board inventory differs')
    if json.loads(args.inventory.read_text()) != {'rows': [{'machine': m} for m in names]}:
        raise ValueError('Frozen closeout inventory differs')
    if sha(args.inventory) != report['inventory_sha256']:
        raise ValueError('Frozen closeout inventory bytes differ')
    path = args.proof_dir/'WeightedCloseout.v'
    write_exact(path, closeout.source(namespace), report['proof_artifacts_sha256'][path.name])
    flags = ['-Q', str(ROOT/'theories'), 'BBB24',
             '-Q', str(args.proof_dir.resolve()), namespace]
    run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(path.resolve())],
        args.proof_dir/'WeightedCloseout.portable.log', args.timeout)
    actual[path.name] = sha(path)
    actual[path.with_suffix('.vo').name] = sha(path.with_suffix('.vo'))
    # Check the imported compiled board itself, not merely adjacent source text.
    # This rejects a stale but valid .vo proving a different machine inventory.
    inventory_theory = ROOT/'theories/BoardManifest.v'
    inventory_theory_hash = sha(inventory_theory)
    inventory_path = args.proof_dir/'WeightedPortableInventory.v'
    inventory_path.write_text(inventory_source(namespace, names))
    run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(inventory_path.resolve())],
        args.proof_dir/'WeightedPortableInventory.log', args.timeout)
    actual[inventory_path.name] = sha(inventory_path)
    actual[inventory_path.with_suffix('.vo').name] = sha(inventory_path.with_suffix('.vo'))
    audit_log = args.proof_dir/'closeout-portable-coqchk.log'
    run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags,
         namespace+'.WeightedPortableInventory'], audit_log, args.timeout)
    if any(sha(args.proof_dir/name) != digest for name, digest in actual.items()):
        raise ValueError('Proof artifacts changed during the fresh audit')
    if sha(args.weighted_report) != source_report_hash or sha(args.report) != report_hash:
        raise ValueError('Frozen reports changed during replay')
    if sha(args.inventory) != report['inventory_sha256']:
        raise ValueError('Inventory changed during replay')
    if legacy.source_hashes() != manifest['source_sha256']:
        raise ValueError('Weighted checker sources changed during replay')
    if sha(inventory_theory) != inventory_theory_hash:
        raise ValueError('Inventory-check theory changed during replay')
    if any(sha(ROOT/'theories'/name) != expected_inputs[key] for name, key in (
            ('Bootstrap.v', 'bootstrap_sha256'), ('Closeout.v', 'closeout_sha256'),
            ('CertifiedBoard.v', 'certified_board_sha256'))):
        raise ValueError('Closeout sources changed during replay')
    receipt = {
        'status': 'Frozen closeout sources compiled and recursively kernel audited.',
        'frozen_report_sha256': report_hash,
        'source_report_sha256': source_report_hash,
        'wrapper_sha256': sha(Path(__file__)),
        'inventory_theory_sha256': inventory_theory_hash,
        'actual_artifacts_sha256': actual,
        'audit_log_sha256': sha(audit_log),
        'families_discharged': len(names)}
    (args.proof_dir/'portable-closeout-replay.json').write_text(serialized(receipt))
    print(f'Replayed {len(names)} census-linked families; frozen reports unchanged.', flush=True)


if __name__ == '__main__':
    main()
