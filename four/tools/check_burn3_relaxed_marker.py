"""Replay the frozen relaxed-marker theorem, regressions and one exact census row.

Handwritten Coq sources live under proof-sources/burn3-relaxed-marker. Replay
copies their exact frozen bytes to an ignored build namespace and adds a Coq
inventory wrapper tied to the compact input. Current objects and the complete
dependency closure are audited; published evidence is never rewritten.
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
OUTPUT = ROOT / 'build/burn3-history-targets/proof'
NAMESPACE = 'BBB24Burn3RelaxedMarker'
PREFIX = ROOT / 'research/burn3-relaxed-marker'
TEMPLATES = ['RelaxedMarker.v', 'Regression.v', 'ExampleBoard.v']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Frozen artifact differs: ' + str(path))
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
    input_path = artifact('input.json')
    report_path, inventory_path = artifact('checked.json'), artifact('machines.json')
    protected = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    data = json.loads(input_path.read_text())
    expected = [{'machine': '1LB2RA2RA1RA_2RB3LB0LB3LA', 'code': 4967611060,
                 'marker_mask': 10, 'weights': [0, 1, 1, 0]}]
    if data['rows'] != expected or data['state_bound'] != 0:
        raise ValueError('Expected the frozen one-family state-zero witness')
    machine = data['rows'][0]['machine']
    if sum(v * 17**i for i, v in enumerate(codes(machine))) != data['rows'][0]['code']:
        raise ValueError('Machine code differs from exact input')
    templates = [ROOT / 'proof-sources/burn3-relaxed-marker' / name for name in TEMPLATES]
    template_pins = {str(p.relative_to(ROOT)): sha(p) for p in templates}
    if template_pins != data['template_sha256']:
        raise ValueError('Frozen handwritten proof template differs')
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [part for directory, namespace in load_paths for part in ('-Q', str(directory), namespace)]
    paths = []
    for template in templates:
        path = OUTPUT / template.name
        exact(path, template.read_text())
        paths.append(path)
    descriptor = {'id': 'burn3_relaxed_marker', 'scope': 'state', 'rows': 1,
        'state_bound': 0, 'instruction_bound': None, 'module': NAMESPACE + '.Inventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NAMESPACE + '.ExampleBoard',
                                  'machines': [machine]}))
    paths.append(path)
    sources = dependency_hashes(paths, flags)
    for name in ('check_burn3_relaxed_marker.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps({'rows': [{'machine': machine}]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'template_sha256': template_pins, 'source_sha256': sources,
              'descriptor': descriptor, 'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': 1, 'checked_instruction_families': 0}
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
        raise ValueError('Frozen input, template or dependency changed during replay')
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
    print('One relaxed-marker state family kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
