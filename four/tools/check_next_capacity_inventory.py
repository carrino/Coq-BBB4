"""Link the new capacity/portfolio inventories exactly to their audited boards."""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import inventory_source, read_inventory
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/next-capacity/inventory-proof'
NAMESPACE = 'BBB24NextCapacityInventory'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    load_paths = [(ROOT / 'theories', 'BBB24'),
                  (ROOT / 'build/next-capacity/capacity-proof', 'BBB24NextCapacity'),
                  (ROOT / 'build/next-capacity/portfolio-proof', 'BBB24NextPortfolio'),
                  (OUTPUT, NAMESPACE)]
    flags = [arg for path, namespace in load_paths for arg in ('-Q', str(path), namespace)]
    inputs = {}
    descriptors, roots, modules, compile_seconds = [], [], [], {}
    for kind, name in (('capacity', 'Capacity'), ('portfolio', 'Portfolio')):
        report_path = ROOT / f'research/next-capacity-{kind}-check.json'
        inventory_path = ROOT / f'research/next-capacity-{kind}-checked-machines.json'
        old = json.loads(report_path.read_text())
        if sha(inventory_path) != old['inventory_sha256']:
            raise ValueError('Changed checked-machine inventory')
        for path in (report_path, inventory_path):
            inputs[str(path.relative_to(ROOT))] = sha(path)
        spec = {'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}
        machines = read_inventory(spec)
        if old['census_linked'] != len(machines) or old['counts'] != {'coq_checked': len(machines)}:
            raise ValueError('Input board is not completely checked')
        original = {**old['descriptor'], 'id': 'next_' + kind, 'scope': 'both',
                    'rows': len(machines), 'state_bound': 4096, 'instruction_bound': 4096,
                    'inventories': [spec], 'machines': machines}
        source = OUTPUT / (name + '.v')
        source.write_text(inventory_source(original))
        started = time.monotonic()
        with source.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(source)],
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=300)
        compile_seconds[name] = round(time.monotonic() - started, 3)
        roots.append(source)
        modules.append(NAMESPACE + '.' + name)
        descriptors.append({'id': 'next_' + kind, 'scope': 'both', 'rows': len(machines),
            'state_bound': 4096, 'instruction_bound': 4096,
            'module': NAMESPACE + '.' + name, 'board': 'board',
            'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
            'inventories': [spec], 'proof_source': str(source.relative_to(ROOT)),
            'exact_inventory_theorem': NAMESPACE + '.' + name + '.inventory_exact',
            'load_paths': [{'path': str(path.relative_to(ROOT)), 'namespace': namespace}
                           for path, namespace in load_paths[1:]]})
        print('Compiled exact inventory ' + name, flush=True)
    for filename in ('check_next_capacity_inventory.py', 'check_campaign.py', 'kernel_audit_cache.py'):
        inputs['tools/' + filename] = sha(ROOT / 'tools' / filename)
    receipt_path, log_path = kernel_audit_cache.fresh_paths(OUTPUT, 'kernel-audit')
    started = time.monotonic()
    kernel_audit_cache.audit(modules, roots, load_paths, receipt_path, log_path,
                             recursive=True, timeout=900)
    if any(sha(ROOT / name) != digest for name, digest in inputs.items()):
        raise ValueError('Inventory inputs changed during proof replay')
    report = {'scope': 'Exact BOTH board inventories, bounds and pending-family linkage.',
              'inputs_sha256': inputs, 'boards': descriptors,
              'exact_inventory_checked_families': sum(board['rows'] for board in descriptors),
              'kernel_receipt': str(receipt_path.relative_to(ROOT)),
              'kernel_receipt_sha256': sha(receipt_path),
              'kernel_audit': 'Full recursive coqchk, no dependency-skipping flags.',
              'compile_seconds': compile_seconds,
              'kernel_audit_seconds': round(time.monotonic() - started, 3),
              'resource_limits': {'workers': 1, 'address_space_bytes': 2147483648,
                                  'compile_timeout_seconds': 300, 'audit_timeout_seconds': 900}}
    path = ROOT / 'research/next-capacity-inventory-check.json'
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('Recursively kernel-audited five exact inventory entries.', flush=True)


if __name__ == '__main__':
    main()
