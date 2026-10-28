"""Portably replay five frozen proofs and their exact inventory wrappers.

Published research files are read-only inputs. Current object hashes, audit
receipts and timings are written only below the chosen build directory.
Historical .vo hashes and historical timing receipts are never replay criteria.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

from check_campaign import inventory_source
import kernel_audit_cache
from replay_portable_weighted import run, serialized, sha, write_exact
from weighted_codec_v2 import bundle_decode

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = 'BBB24NextCapacityInventory'
KINDS = (('capacity', 'Capacity', 'BBB24NextCapacity', 1),
         ('portfolio', 'Portfolio', 'BBB24NextPortfolio', 4))
# Exact source bytes from the separately audited frozen inventory wrappers.
WRAPPER_SHA256 = {
    'Capacity': 'e010ea86e91075ea6f44837915448700cb44c8c4dbb211f35897ff48ad78dd77',
    'Portfolio': 'c735ca904e6494758addd53a72a48f4e1cc3ec03580474f8367ecf3cac6daad2'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def research(name):
    return ROOT / ('research/next-capacity-' + name)


def published_snapshot():
    return {str(path.relative_to(ROOT)): sha(path)
            for path in sorted((ROOT / 'research').glob('next-capacity*')) if path.is_file()}


def frozen_load_paths():
    return [{'path': 'build/next-capacity/' + kind + '-proof', 'namespace': namespace}
            for kind, _, namespace, _ in KINDS] + [
                {'path': 'build/next-capacity/inventory-proof', 'namespace': NAMESPACE}]


def exact_descriptor(kind, name, count):
    return {'id': 'next_' + kind, 'scope': 'both', 'rows': count,
            'state_bound': 4096, 'instruction_bound': 4096,
            'module': NAMESPACE + '.' + name, 'board': 'board',
            'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
            'inventories': [{'path': 'research/next-capacity-' + kind + '-checked-machines.json',
                             'format': 'rows'}],
            'proof_source': 'build/next-capacity/inventory-proof/' + name + '.v',
            'exact_inventory_theorem': NAMESPACE + '.' + name + '.inventory_exact',
            'load_paths': frozen_load_paths()}


def validate_contract(kind, report, inventory, descriptor):
    """Check portable, typed claims without consulting historical object hashes."""
    _, name, namespace, count = next(row for row in KINDS if row[0] == kind)
    manifest = report['manifest']
    for field, value in (('rows', count), ('state_bound', 4096),
                         ('instruction_bound', 4096), ('batch_size', 1)):
        require(type(manifest[field]) is int and manifest[field] == value,
                'Unexpected typed manifest field: ' + field)
    require(manifest['namespace'] == namespace, 'Unexpected source namespace')
    require(type(report['census_linked']) is int and report['census_linked'] == count,
            'Unexpected census-linked count')
    require(report['counts'] == {'coq_checked': count}
            and type(report['counts']['coq_checked']) is int, 'Incomplete certificate checks')
    require(len(report['results']) == count, 'Unexpected result count')
    names = [row['machine'] for row in report['results']]
    require(len(set(names)) == count, 'Repeated checked machine')
    for index, row in enumerate(report['results']):
        require(row == {'kind': 'weighted', 'machine': names[index],
                        'module': f'Weighted{index:05d}', 'status': 'coq_checked'},
                'Unexpected result mapping')
    require(inventory == {'rows': [{'machine': machine} for machine in names]},
            'Ordered checked inventory differs')
    for field, value in (('rows', count), ('state_bound', 4096), ('instruction_bound', 4096)):
        require(type(descriptor[field]) is int and descriptor[field] == value,
                'Unexpected typed inventory field: ' + field)
    require(descriptor == exact_descriptor(kind, name, count), 'Exact inventory descriptor differs')
    expected_original = {
        'board': 'weighted_board', 'discharged': 'weighted_families_discharged',
        'load_paths': [{'path': 'build/next-capacity/' + kind + '-proof', 'namespace': namespace}],
        'machine_inputs': [{'format': 'json_rows',
                            'path': 'research/next-capacity-' + kind + '-checked-machines.json'}],
        'module': namespace + '.WeightedAll', 'nonhalt': 'weighted_board_nonhalt',
        'proof_source': 'build/next-capacity/' + kind + '-proof/WeightedAll.v',
        'small_sound': 'weighted_board_small_sound', 'sound': 'weighted_board_sound',
        'was_pending': 'weighted_board_was_pending'}
    require(report['descriptor'] == expected_original, 'Original proof descriptor differs')
    original = {**expected_original, 'id': 'next_' + kind, 'scope': 'both',
                'rows': count, 'state_bound': 4096, 'instruction_bound': 4096,
                'inventories': descriptor['inventories'], 'machines': names}
    text = inventory_source(original)
    require(hashlib.sha256(text.encode()).hexdigest() == WRAPPER_SHA256[name],
            'Regenerated exact inventory source differs')
    return text


def load_evidence(output):
    frozen = json.loads(research('inventory-check.json').read_text())
    require(type(frozen['exact_inventory_checked_families']) is int
            and frozen['exact_inventory_checked_families'] == 5, 'Unexpected exact inventory size')
    require([board['id'] for board in frozen['boards']] == ['next_capacity', 'next_portfolio'],
            'Unexpected exact inventory boards or order')
    for filename, digest in frozen['inputs_sha256'].items():
        require(sha(ROOT / filename) == digest, 'Frozen inventory input differs: ' + filename)
    evidence = []
    for (kind, name, namespace, count), descriptor in zip(KINDS, frozen['boards']):
        report_path = research(kind + '-check.json')
        registry_path = research(kind + '-registry.json')
        inventory_path = research(kind + '-checked-machines.json')
        report = json.loads(report_path.read_text())
        registry = json.loads(registry_path.read_text())
        inventory = json.loads(inventory_path.read_text())
        require(sha(registry_path) == report['manifest']['registry_sha256'], 'Registry hash differs')
        require(sha(inventory_path) == report['inventory_sha256'], 'Inventory hash differs')
        for filename, digest in report['manifest']['sources_sha256'].items():
            require(sha(ROOT / filename) == digest, 'Frozen proof source differs: ' + filename)
        rows = []
        for bundle in registry['bundles']:
            bundle_path = ROOT / bundle['path']
            require(sha(bundle_path) == bundle['sha256'], 'Compact certificate hash differs')
            decoded = bundle_decode(bundle_path.read_text())
            require(len(decoded) == bundle['rows'], 'Compact certificate row count differs')
            rows.extend(decoded)
        require(type(registry['rows']) is int and registry['rows'] == count
                and len(rows) == count, 'Registry row count differs')
        require([row['machine'] for row in rows] == [row['machine'] for row in inventory['rows']],
                'Certificate and checked inventory orders differ')
        text = validate_contract(kind, report, inventory, descriptor)
        # Read existing source bytes only; never use historical .vo or audit receipts.
        for path in (ROOT / descriptor['proof_source'], output / 'inventory-proof' / (name + '.v')):
            if path.exists():
                require(sha(path) == WRAPPER_SHA256[name], 'Existing exact inventory source differs: ' + str(path))
        evidence.append({'kind': kind, 'name': name, 'namespace': namespace, 'count': count,
                         'report_path': report_path, 'registry_path': registry_path,
                         'inventory_path': inventory_path, 'descriptor': descriptor, 'text': text})
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'build/next-capacity/portable-replay')
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=900)
    parser.add_argument('--preflight', action='store_true', help='Validate frozen inputs and sources; no writes or compilation')
    args = parser.parse_args()
    require(args.timeout > 0 and args.audit_timeout > 0, 'Positive timeouts required')
    output = args.output_dir.resolve()
    require(output.is_relative_to((ROOT / 'build').resolve()), 'Output must remain below four/build')
    before = published_snapshot()
    try:
        evidence = load_evidence(output)
        version = subprocess.check_output(['coqc', '--version'], text=True).splitlines()[0]
        require(all(json.loads(row['report_path'].read_text())['manifest']['coq_version'] == version
                    for row in evidence), 'Coq version differs from frozen proofs')
        if args.preflight:
            print('Preflight passed: five frozen proofs and two exact wrappers; no compilation or writes.')
            return
        resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
        output.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        proof_receipts = {}
        for row in evidence:
            directory = output / (row['kind'] + '-proof')
            command = [sys.executable, str(ROOT / 'tools/replay_portable_weighted.py'),
                       '--report', str(row['report_path']), '--registry', str(row['registry_path']),
                       '--inventory', str(row['inventory_path']), '--output-dir', str(directory),
                       '--timeout', str(args.timeout)]
            run(command, output / (row['kind'] + '-replay.log'), args.timeout * (2 * row['count'] + 3))
            receipt_path = directory / 'portable-replay.json'
            receipt = json.loads(receipt_path.read_text())
            require(receipt['frozen_report_sha256'] == sha(row['report_path'])
                    and receipt['checked_families'] == row['count'], 'Portable proof replay receipt differs')
            proof_receipts[row['kind']] = {'path': str(receipt_path.relative_to(ROOT)), 'sha256': sha(receipt_path)}
            require(published_snapshot() == before, 'Published research files changed during proof replay')
            print('Portably replayed ' + row['kind'] + ': ' + str(row['count']) + ' checked families.', flush=True)
        exact_dir = output / 'inventory-proof'
        exact_dir.mkdir(parents=True, exist_ok=True)
        load_paths = [(ROOT / 'theories', 'BBB24')]
        load_paths += [(output / (row['kind'] + '-proof'), row['namespace']) for row in evidence]
        load_paths.append((exact_dir, NAMESPACE))
        flags = [arg for path, namespace in load_paths for arg in ('-Q', str(path), namespace)]
        roots, modules, descriptors = [], [], []
        for row in evidence:
            source = exact_dir / (row['name'] + '.v')
            write_exact(source, row['text'], WRAPPER_SHA256[row['name']])
            run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(source)],
                source.with_suffix('.portable.log'), args.timeout)
            roots.append(source)
            modules.append(NAMESPACE + '.' + row['name'])
            descriptor = deepcopy(row['descriptor'])
            descriptor['proof_source'] = str(source.relative_to(ROOT))
            descriptor['load_paths'] = [{'path': str(path.relative_to(ROOT)), 'namespace': namespace}
                                        for path, namespace in load_paths[1:]]
            descriptors.append(descriptor)
        receipt_path, audit_log = kernel_audit_cache.fresh_paths(exact_dir, 'portable-kernel-audit')
        kernel_audit_cache.audit(modules, roots, load_paths, receipt_path, audit_log,
                                 recursive=True, timeout=args.audit_timeout)
        load_evidence(output)
        receipt = {'status': 'Five frozen proofs and two exact inventory wrappers freshly kernel-audited.',
                   'frozen_research_sha256': before, 'adapter_sha256': sha(Path(__file__)),
                   'portable_weighted_replayer_sha256': sha(ROOT / 'tools/replay_portable_weighted.py'),
                   'boards': descriptors, 'exact_inventory_checked_families': 5,
                   'portable_proof_receipts': proof_receipts,
                   'exact_inventory_source_sha256': WRAPPER_SHA256,
                   'kernel_receipt': str(receipt_path.relative_to(ROOT)), 'kernel_receipt_sha256': sha(receipt_path),
                   'resource_limits': {'workers': 1, 'address_space_bytes': 2147483648},
                   'seconds': round(time.monotonic() - started, 3)}
        (output / 'portable-next-capacity.json').write_text(serialized(receipt))
        print('Portable next-capacity replay passed; all published research files are unchanged.', flush=True)
    finally:
        require(published_snapshot() == before, 'Published next-capacity research files changed')


if __name__ == '__main__':
    main()
