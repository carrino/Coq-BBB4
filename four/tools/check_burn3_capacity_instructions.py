"""Replay the two history certificates from capacity instruction diagnostics.

Uses existing AdvancedPipeline proofs and adds exact census-board inventory.
Published reports remain frozen on replay; current runtime evidence stays in
the ignored build directory. No discovery executable is needed for replay.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

import check_closure_wave as engine
from check_campaign import dependency_hashes, inventory_source
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn3-capacity-instruction/proof'
PREFIX = ROOT / 'research/burn3-capacity-instruction'
NAMESPACE = 'BBB24Burn3CapacityInstruction'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Frozen source or inventory differs: ' + str(path))
    if not path.exists():
        path.write_text(contents)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        parser.error('Replay budgets must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path, report_path, inventory_path = artifact('input.json'), artifact('checked.json'), artifact('machines.json')
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    data, rows = engine.load_input(input_path)
    if len(rows) != 2 or any(row['mode'] != 'hist' or row['bound'] != 4096 for row in rows):
        raise ValueError('Expected exactly two history rows at bound4096')
    search_path = ROOT / data['source_report']
    expected = json.loads(search_path.read_text())['candidates']
    if rows != sorted(expected, key=engine.machine_hash):
        raise ValueError('Proof selection differs from frozen search inventory')
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in (input_path, search_path)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [value for directory, namespace in load_paths for value in ('-Q', str(directory), namespace)]
    paths, modules = [], []
    for index, row in enumerate(rows):
        name = f'History{index:03d}'
        path = OUTPUT / (name + '.v')
        exact(path, engine.shard_source([row]))
        paths.append(path); modules.append(name)
    path = OUTPUT / 'All.v'
    exact(path, engine.aggregate_source(modules, NAMESPACE, 4096, len(rows)))
    paths.append(path)
    descriptor = {'id': 'burn3_capacity_instruction', 'scope': 'both', 'rows': len(rows),
        'state_bound': 4096, 'instruction_bound': 4096, 'module': NAMESPACE + '.Inventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NAMESPACE + '.All',
                                  'machines': [row['machine'] for row in rows]}))
    paths.append(path)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn3_capacity_instructions.py', 'check_closure_wave.py',
                     'check_campaign.py', 'kernel_audit_cache.py',
                     'generate_pipeline_examples.py', 'check_shadow_links.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources, 'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': len(rows), 'checked_instruction_families': len(rows)}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen proof evidence differs')
    if previous and sha(inventory_path) != stable['inventory_sha256']:
        raise ValueError('Frozen inventory differs')
    timings = {}
    for path in paths:
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - start, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache.fresh_paths(OUTPUT, 'kernel-audit')
    kernel_audit_cache.audit([NAMESPACE + '.Inventory'], [paths[-1]], load_paths,
                             receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **sources}.items()):
        raise ValueError('Inputs changed during proof replay')
    current = {**stable, 'scope': 'Exact state and instruction census bounds; all completions covered.',
               'compile_seconds': timings, 'kernel_receipt': str(receipt.relative_to(ROOT)),
               'kernel_receipt_sha256': sha(receipt), 'kernel_audit': 'Full recursive coqchk.',
               'object_sha256': {str(path.with_suffix('.vo').relative_to(ROOT)):
                                sha(path.with_suffix('.vo')) for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Two capacity instruction families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
