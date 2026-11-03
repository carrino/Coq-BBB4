"""Replay a universal boundary counter with all eight instructions recurrent.

The exact family receives both bounds zero for every completion. Original
pending membership and the board inventory are kernel-checked. Native traces
are selection provenance only and are unnecessary for replay.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import ROOT, dependency_hashes, inventory_source, packed, sha
from instruction_residual import residual
import kernel_audit_cache_v3 as kernel

PREFIX = ROOT / 'research/instruction-sparse-return'
BUILD = ROOT / 'build/instruction-sparse-return/proof'
NS = 'BBB24SparseReturn'
MACHINE = '1LB2LB3RA3LB_1RB1LA3RA1RA'


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    inp, report, inv = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    if (data['rows'] != [dict(id='tr24-2806290152', machine=MACHINE, code=packed(MACHINE))] or
            data['state_bound'] != 0 or data['instruction_bound'] != 0):
        raise ValueError('Unexpected sparse-return family or bound')
    remaining, pins = residual(ROOT / data['baseline_report'], data['baseline_sha256'])
    if MACHINE not in remaining:
        raise ValueError('Sparse-return family is outside the frozen instruction remainder')
    pins[str(inp.relative_to(ROOT))] = sha(inp)
    diagnostic = ROOT / data['source_diagnostics']
    if sha(diagnostic) != data['source_diagnostics_sha256']:
        raise ValueError('Original instruction diagnostic differs')
    original = next(row for row in json.loads(diagnostic.read_text())['rows'] if row['machine'] == MACHINE)
    if original['missing_any_witness'] != [0]:
        raise ValueError('Unexpected historical diagnostic target')
    pins[str(diagnostic.relative_to(ROOT))] = sha(diagnostic)
    BUILD.mkdir(parents=True, exist_ok=True)
    paths = []
    for name in ('BoundaryCounter.v', 'Regression.v', 'Board.v'):
        source = ROOT / 'proof-sources/instruction-sparse-return' / name
        expected = data['templates_sha256'][str(source.relative_to(ROOT))]
        if sha(source) != expected:
            raise ValueError('Frozen sparse-return proof differs: ' + str(source))
        pins[str(source.relative_to(ROOT))] = expected
        target = BUILD / name
        exact(target, source.read_text())
        paths.append(target)
    descriptor = dict(id='instruction_sparse_return', scope='both', rows=1,
        module=NS + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        was_pending='was_pending', state_bound=0, instruction_bound=0,
        exact_inventory_theorem=NS + '.Inventory.inventory_exact',
        proof_source=str((BUILD / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(inv.relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(BUILD.relative_to(ROOT)), namespace=NS)])
    path = BUILD / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NS + '.Board', 'machines': [MACHINE]}) +
          '\nRequire Import ' + NS + '.Regression.\n')
    paths.append(path)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (BUILD, NS)]
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    sources = dependency_hashes(paths, flags)
    for name in ('check_instruction_sparse_return.py', 'instruction_residual.py', 'check_campaign.py',
                 'check_shadow_links.py', 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps(dict(rows=[dict(machine=MACHINE)]), indent=2) + '\n'
    stable = dict(inputs_sha256=pins, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
        checked_instruction_families=1, checked_state_families=1,
        new_instruction_families=1, new_state_families=0)
    previous = json.loads(report.read_text()) if report.exists() else None
    protected = {p: sha(p) for p in (report, inv) if p.exists()}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen sparse-return report differs from replay inputs')
    if previous and (not inv.exists() or sha(inv) != stable['inventory_sha256']):
        raise ValueError('Frozen sparse-return inventory differs')
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic()-started, 3)
        print('Compiled ' + path.stem, flush=True)
    receipt, log = kernel.fresh_paths(BUILD, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory'], [paths[-1]], loadpaths,
                         receipt, log, recursive=True, timeout=args.audit_timeout)
    if NS + '.Regression' not in audit['checked_modules']:
        raise ValueError('Kernel audit omitted sparse-return regressions')
    if any(sha(ROOT / name) != expected for name, expected in {**pins, **sources}.items()):
        raise ValueError('Sparse-return source or input changed during replay')
    if any(sha(p) != expected for p, expected in protected.items()):
        raise ValueError('Published sparse-return evidence changed during replay')
    current = dict(stable, scope='Exact both-bound census family; every completion covered.',
        kernel_audit='Full recursive coqchk including regressions; no skipped dependencies.',
        compile_seconds=timings, audit_seconds=round(time.monotonic()-started, 3),
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        checked_modules=len(audit['checked_modules']), reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in paths})
    if previous is None:
        exact(inv, inventory)
        exact(report, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (BUILD / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('One sparse-return instruction family fully kernel-audited.', flush=True)


if __name__ == '__main__':
    main()
