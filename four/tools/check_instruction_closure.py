"""Replay an instruction closure batch and recursively audit its exact board.

Existing AdvancedPipeline certificates prove both bounds for every completion.
Discovery is unnecessary for replay. Frozen reports are preserved; current
execution receipts and generated Coq sources remain below build/.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time

import check_closure_wave as closure
from check_campaign import ROOT, dependency_hashes, inventory_source, sha
from instruction_residual import residual
import kernel_audit_cache_v3 as kernel


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name', default='instruction-burn1')
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    if not re.fullmatch(r'instruction-burn[1-9][0-9]*', args.name):
        parser.error('Expected instruction-burn followed by a positive integer')
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive timeouts required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    prefix = ROOT / 'research' / args.name
    artifact = lambda suffix: prefix.with_name(prefix.name + '-' + suffix)
    build = ROOT / 'build' / args.name / 'proof'
    namespace = 'BBB24InstructionBurn' + args.name.removeprefix('instruction-burn')
    build.mkdir(parents=True, exist_ok=True)
    input_path, report_path, inventory_path = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(input_path.read_text())
    remaining, pins = residual(ROOT / data['baseline_report'], data['baseline_sha256'])
    pins[str(input_path.relative_to(ROOT))] = sha(input_path)
    rows = data['rows']
    if not rows or len(rows) != data['selected_rows']:
        raise ValueError('Empty or incomplete proof selection')
    if rows != sorted(rows, key=closure.machine_hash):
        raise ValueError('Proof rows must be in machine SHA256 order')
    machines = [row['machine'] for row in rows]
    if len(set(machines)) != len(machines) or not set(machines) <= remaining:
        raise ValueError('Repeated target or previously covered instruction family')
    for row in rows:
        closure.validate_row(row)
    bound = rows[0]['bound']
    if any(row['bound'] != bound for row in rows):
        raise ValueError('Batch bounds must agree')
    search = ROOT / data['search_report']
    if sha(search) != data['search_sha256']:
        raise ValueError('Discovery report differs')
    discovery = json.loads(search.read_text())
    if rows != sorted(discovery['candidates'], key=closure.machine_hash):
        raise ValueError('Proof selection differs from native candidates')
    pins[str(search.relative_to(ROOT))] = sha(search)
    paths, modules = [], []
    for index, row in enumerate(rows):
        name = f'History{index:03d}'
        path = build / (name + '.v')
        exact(path, closure.shard_source([row]))
        paths.append(path)
        modules.append(name)
    path = build / 'All.v'
    exact(path, closure.aggregate_source(modules, namespace, bound, len(rows)))
    paths.append(path)
    descriptor = dict(id=args.name.replace('-', '_'), scope='both', rows=len(rows),
        module=namespace + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        nonhalt='nonhalt', was_pending='was_pending', state_bound=bound, instruction_bound=bound,
        exact_inventory_theorem=namespace + '.Inventory.inventory_exact',
        proof_source=str((build / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(inventory_path.relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(build.relative_to(ROOT)), namespace=namespace)])
    path = build / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': namespace + '.All', 'machines': machines}))
    paths.append(path)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (build, namespace)]
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    sources = dependency_hashes(paths, flags)
    for filename in ('check_instruction_closure.py', 'instruction_residual.py',
                     'check_closure_wave.py', 'check_campaign.py', 'check_shadow_links.py',
                     'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps(dict(rows=[dict(machine=m) for m in machines]), indent=2) + '\n'
    stable = dict(inputs_sha256=pins, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
        checked_instruction_families=len(rows), checked_state_families=len(rows),
        new_instruction_families=len(rows), new_state_families=0,
        baseline_instruction_remaining=len(remaining), instruction_remaining=len(remaining)-len(rows))
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    protected = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen proof report differs from replay inputs')
    if previous and (not inventory_path.exists() or sha(inventory_path) != stable['inventory_sha256']):
        raise ValueError('Frozen exact inventory differs')
    if args.generate_only:
        print(json.dumps(dict(generated_modules=len(paths), targets=len(rows), proof_credit=False)))
        return
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - started, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel.fresh_paths(build, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([namespace + '.Inventory'], [paths[-1]], loadpaths,
                         receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != expected for name, expected in {**pins, **sources}.items()):
        raise ValueError('Proof source or input changed during replay')
    if any(sha(path) != expected for path, expected in protected.items()):
        raise ValueError('Published evidence changed during replay')
    current = dict(stable, scope='Exact both-bound census families; every completion covered.',
        kernel_audit='Full recursive coqchk; no admitted or skipped dependencies.',
        compile_seconds=timings, audit_seconds=round(time.monotonic()-started, 3),
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        checked_modules=len(audit['checked_modules']), reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in paths})
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (build / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print(f'{len(rows)} new instruction families fully kernel-audited; '
          f'{stable["instruction_remaining"]} remain in the frozen hard cohort.', flush=True)


if __name__ == '__main__':
    main()
