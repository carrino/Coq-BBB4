"""Freshly replay the nine diagnostic history certificates with exact inventory.

Uses the frozen StatePipeline renderer and proof checker. Research files are
published once; later replays preserve them and record current object hashes
and full recursive audit receipts under the ignored canonical build directory.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time
from types import SimpleNamespace

from check_campaign import dependency_hashes, inventory_source
import check_state_pipeline_batch as engine
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn2-diagnostic-short/proof'
PREFIX = ROOT / 'research/burn2-diagnostic-short'
NAMESPACE = 'BBB24Burn2DiagnosticShort'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(file, text):
    if file.exists() and file.read_text() != text:
        raise ValueError('Frozen proof source or inventory differs: ' + str(file))
    if not file.exists():
        file.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    report_path, inventory_path = path('checked.json'), path('machines.json')
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    input_path = path('proof-input.json')
    data, groups = engine.load(SimpleNamespace(input=input_path))
    assert data['selected_rows'] == 9 and data['state_bound'] == 4096
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path),
              data['source_report']: sha(ROOT / data['source_report'])}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [value for directory, namespace in load_paths for value in ('-Q', str(directory), namespace)]
    paths, modules, machines = [], [], []
    for group in groups:
        for packed in group['rows']:
            name = f'History{len(modules):03d}'
            source = OUTPUT / (name + '.v')
            exact(source, engine.shard_text([packed], group['certificate'], 4096))
            modules.append(name); paths.append(source); machines.append(engine.unpack(packed))
    source = OUTPUT / 'HistoryAll.v'
    exact(source, engine.aggregate(modules, len(machines), 4096, NAMESPACE))
    paths.append(source)
    descriptor = {'id': 'burn2_diagnostic_history', 'scope': 'state', 'rows': len(machines),
        'state_bound': 4096, 'instruction_bound': None, 'module': NAMESPACE + '.HistoryInventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'HistoryInventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.HistoryInventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    original = {**descriptor, 'module': NAMESPACE + '.HistoryAll', 'board': 'state_board',
                'small_sound': 'state_board_small', 'sound': 'state_board_bound',
                'was_pending': 'state_board_pending', 'machines': machines}
    source = OUTPUT / 'HistoryInventory.v'
    exact(source, inventory_source(original))
    paths.append(source)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn2_diagnostic.py', 'check_state_pipeline_batch.py', 'check_campaign.py',
                     'kernel_audit_cache.py', 'generate_pipeline_examples.py', 'check_shadow_links.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': machine} for machine in machines]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources, 'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': len(machines), 'checked_instruction_families': 0}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen diagnostic proof evidence differs')
    if previous and sha(inventory_path) != stable['inventory_sha256']:
        raise ValueError('Frozen diagnostic inventory differs')
    timings = {}
    for source in paths:
        start = time.monotonic()
        with source.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(source)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[source.stem] = round(time.monotonic() - start, 3)
        print('Compiled ' + source.stem + ': ' + str(timings[source.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache.fresh_paths(OUTPUT, 'kernel-audit')
    kernel_audit_cache.audit([NAMESPACE + '.HistoryInventory'], [paths[-1]], load_paths,
                             receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **sources}.items()):
        raise ValueError('Inputs changed during diagnostic proof replay')
    current = {**stable, 'scope': 'Exact state-only census bound; no instruction claim.',
               'compile_seconds': timings, 'kernel_receipt': str(receipt.relative_to(ROOT)),
               'kernel_receipt_sha256': sha(receipt), 'kernel_audit': 'Full recursive coqchk.',
               'object_sha256': {str(source.with_suffix('.vo').relative_to(ROOT)):
                                sha(source.with_suffix('.vo')) for source in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Nine diagnostic history families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
