"""Replay the targeted refinement certificates and exact census inventories.

The first run publishes checked reports. Subsequent runs use the portable
weighted adapter and write fresh runtime evidence below the build directory;
published evidence and previous proof objects are never replay prerequisites.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

from check_campaign import inventory_source, read_inventory
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn2-capacity'
PREFIX = ROOT / 'research/burn2-capacity'
NAMESPACE = 'BBB24Burn2CapacityInventory'
CHECKERS = {'ordinary': 'record_weighted_audit.py', 'weighted': 'record_weighted_audit.py',
            'capacity': 'check_weighted_capacity_v2.py', 'portfolio': 'check_weighted_portfolio.py'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def research(name):
    return PREFIX.with_name(PREFIX.name + '-' + name)


def run(command, log, timeout):
    with log.open('w') as stream:
        subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=timeout)


def validate_published_inputs(frozen):
    if any(sha(ROOT / path) != digest for path, digest in frozen['inputs_sha256'].items()):
        raise ValueError('Published proof inputs changed')


def validate_replayed_contract(frozen, descriptors, report_inputs, output):
    canonical = json.loads(json.dumps(descriptors).replace(
        str(output.relative_to(ROOT)), str(BASE.relative_to(ROOT))))
    if canonical != frozen['boards'] or report_inputs != frozen['inputs_sha256']:
        raise ValueError('Replayed board contract differs from publication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=BASE)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if not output.is_relative_to((ROOT / 'build').resolve()):
        raise ValueError('Proof output must be below four/build')
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    output.mkdir(parents=True, exist_ok=True)
    output_inventory = output / 'inventory-proof'
    output_inventory.mkdir(parents=True, exist_ok=True)
    publication = research('inventory-check.json')
    replay = publication.exists()
    frozen = json.loads(publication.read_text()) if replay else None
    if frozen:
        validate_published_inputs(frozen)
    protected = {str(p): sha(p) for p in PREFIX.parent.glob(PREFIX.name + '*') if p.is_file()}
    report_inputs, originals, descriptors, roots, modules = {}, [], [], [], []
    load_paths = [(ROOT / 'theories', 'BBB24')]
    start = time.monotonic()
    for kind, checker in CHECKERS.items():
        registry = research(kind + '-registry.json')
        if not registry.exists():
            continue
        count = json.loads(registry.read_text())['rows']
        report_path = research(kind + '-check.json')
        inventory = research(kind + '-checked-machines.json')
        namespace = 'BBB24Burn2Capacity' + kind.title()
        proof = output / (kind + '-proof')
        proof.mkdir(parents=True, exist_ok=True)
        if report_path.exists():
            command = [sys.executable, str(ROOT / 'tools/replay_portable_weighted.py'),
                       '--report', str(report_path), '--registry', str(registry),
                       '--inventory', str(inventory), '--output-dir', str(proof),
                       '--timeout', str(args.timeout)]
        else:
            if replay or output != BASE.resolve():
                raise ValueError('Missing published input for portable replay')
            command = [sys.executable, str(ROOT / 'tools' / checker),
                       '--registry', str(registry), '--report', str(report_path),
                       '--inventory', str(inventory), '--output-dir', str(proof),
                       '--namespace', namespace, '--batch-size', '1', '--timeout', str(args.timeout)]
        run(command, output / (kind + '-replay.log'), args.timeout * (2 * count + 4))
        report = json.loads(report_path.read_text())
        machines = read_inventory({'path': str(inventory.relative_to(ROOT)), 'format': 'rows'})
        if report['counts'] != {'coq_checked': count} or report['census_linked'] != count or len(machines) != count:
            raise ValueError('Incomplete certificate proof: ' + kind)
        for path in (registry, report_path, inventory):
            report_inputs[str(path.relative_to(ROOT))] = sha(path)
        original = {**report['descriptor'], 'id': 'burn2_capacity_' + kind,
                    'scope': 'both', 'rows': count, 'state_bound': 4096, 'instruction_bound': 4096,
                    'inventories': [{'path': str(inventory.relative_to(ROOT)), 'format': 'rows'}],
                    'machines': machines}
        originals.append((kind, original))
        load_paths.append((proof, namespace))
        print('Kernel checked ' + kind + ': ' + str(count), flush=True)
    if not originals:
        raise ValueError('No compact certificates')
    load_paths.append((output_inventory, NAMESPACE))
    flags = [arg for path, namespace in load_paths for arg in ('-Q', str(path), namespace)]
    for kind, original in originals:
        name = kind.title()
        source = output_inventory / (name + '.v')
        text = inventory_source(original)
        if source.exists() and source.read_text() != text:
            raise ValueError('Existing inventory source differs')
        source.write_text(text)
        run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(source)],
            source.with_suffix('.log'), args.timeout)
        roots.append(source)
        modules.append(NAMESPACE + '.' + name)
        descriptors.append({'id': original['id'], 'scope': 'both', 'rows': original['rows'],
            'state_bound': 4096, 'instruction_bound': 4096,
            'module': NAMESPACE + '.' + name, 'board': 'board', 'small_sound': 'small_sound',
            'sound': 'sound', 'was_pending': 'was_pending', 'inventories': original['inventories'],
            'proof_source': str(source.relative_to(ROOT)),
            'exact_inventory_theorem': NAMESPACE + '.' + name + '.inventory_exact',
            'load_paths': [{'path': str(path.relative_to(ROOT)), 'namespace': namespace}
                           for path, namespace in load_paths[1:]]})
    receipt, log = kernel_audit_cache.fresh_paths(output_inventory, 'kernel-audit')
    kernel_audit_cache.audit(modules, roots, load_paths, receipt, log, recursive=True,
                             timeout=args.audit_timeout)
    for filename in ('check_burn2_capacity.py', 'check_campaign.py', 'kernel_audit_cache.py'):
        report_inputs['tools/' + filename] = sha(ROOT / 'tools' / filename)
    if any(sha(Path(path)) != digest for path, digest in protected.items()):
        raise ValueError('Published evidence changed during replay')
    result = {'scope': 'Kernel-checked both-bound families with exact census inventories.',
              'inputs_sha256': report_inputs, 'boards': descriptors,
              'exact_inventory_checked_families': sum(board['rows'] for board in descriptors),
              'kernel_receipt': str(receipt.relative_to(ROOT)), 'kernel_receipt_sha256': sha(receipt),
              'kernel_audit': 'Complete recursive coqchk; no dependency-skipping flags.',
              'wall_seconds': round(time.monotonic() - start, 3),
              'resource_limits': {'workers': 1, 'address_space_bytes': 2147483648}}
    if frozen:
        validate_replayed_contract(frozen, descriptors, report_inputs, output)
    if not replay:
        save(publication, result)
    save(output / 'current-proof-receipt.json', result)
    print(json.dumps({'checked_families': result['exact_inventory_checked_families'],
                      'receipt': str(receipt)}), flush=True)


if __name__ == '__main__':
    main()
