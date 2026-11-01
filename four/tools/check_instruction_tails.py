"""Rebuild four frozen finite prefixes and audit their new instruction tails.

Original source bytes are copied into isolated build directories. No previous
generated source, compiled object, native trace or audit receipt is required.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import ROOT, dependency_hashes, inventory_source, read_inventory, sha
from check_instruction_closure import exact
from instruction_residual import residual
import kernel_audit_cache_v3 as kernel

BUILD = ROOT / 'build/instruction-tails'
PREFIX = ROOT / 'research/instruction-tails'
NS = 'BBB24InstructionTails'


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive timeouts required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    inp, report, inv = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    remaining, pins = residual(ROOT / data['baseline_report'], data['baseline_sha256'])
    pins[str(inp.relative_to(ROOT))] = sha(inp)
    previous_path = ROOT / data['previous_batch']
    if sha(previous_path) != data['previous_batch_sha256']:
        raise ValueError('Previous instruction batch report differs')
    previous = json.loads(previous_path.read_text())
    if previous['baseline_instruction_remaining'] != len(remaining):
        raise ValueError('Previous instruction batch uses another baseline')
    spec = previous['descriptor']['inventories'][0]
    previous_inventory = ROOT / spec['path']
    if sha(previous_inventory) != previous['inventory_sha256']:
        raise ValueError('Previous instruction inventory differs')
    prior = set(read_inventory(spec))
    machines = [row['machine'] for row in data['rows']]
    if (len(machines) != 4 or len(set(machines)) != 4 or
            not set(machines) <= remaining - prior or not prior <= remaining or
            len(prior) != previous['new_instruction_families']):
        raise ValueError('Incomplete, repeated or previously covered tail selection')
    pins[str(previous_path.relative_to(ROOT))] = sha(previous_path)
    pins[str(previous_inventory.relative_to(ROOT))] = sha(previous_inventory)
    build = BUILD / 'proof'
    build.mkdir(parents=True, exist_ok=True)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (build, NS)]
    paths = []
    for source in data['sources']:
        proof_input = ROOT / source['proof_input']
        if sha(proof_input) != source['proof_input_sha256']:
            raise ValueError('Original state proof input differs')
        pins[str(proof_input.relative_to(ROOT))] = sha(proof_input)
        original = json.loads(proof_input.read_text())
        directory = BUILD / 'sources' / source['name']
        directory.mkdir(parents=True, exist_ok=True)
        loadpaths.append((directory, source['namespace']))
        for spec in source['files']:
            path = ROOT / spec['path']
            if original['template_sha256'][spec['path']] != spec['sha256'] or sha(path) != spec['sha256']:
                raise ValueError('Original proof source differs: ' + str(path))
            pins[spec['path']] = spec['sha256']
            target = directory / path.name
            exact(target, path.read_text())
            paths.append(target)
    for name in ('SingleInstruction.v', 'FiniteTails.v', 'Board.v', 'Regression.v'):
        source = ROOT / 'proof-sources/instruction-tails' / name
        expected = data['templates_sha256'][str(source.relative_to(ROOT))]
        if sha(source) != expected:
            raise ValueError('New instruction proof template differs')
        pins[str(source.relative_to(ROOT))] = expected
        target = build / name
        exact(target, source.read_text())
        paths.append(target)
    bound = data['instruction_bound']
    if bound != 72057594037927936:
        raise ValueError('Unexpected finite-tail ledger bound')
    descriptor = dict(id='instruction_tails', scope='both', rows=4,
        module=NS + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        nonhalt='nonhalt', was_pending='was_pending', state_bound=bound, instruction_bound=bound,
        exact_inventory_theorem=NS + '.Inventory.inventory_exact',
        proof_source=str((build / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(inv.relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(p.relative_to(ROOT)), namespace=ns) for p, ns in loadpaths[1:]])
    inventory = json.dumps(dict(rows=[dict(machine=m) for m in machines]), indent=2) + '\n'
    path = build / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NS + '.Board', 'machines': machines}) +
          '\nRequire Import ' + NS + '.Regression.\n')
    paths.append(path)
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    sources = dependency_hashes(paths, flags)
    for name in ('check_instruction_tails.py', 'check_instruction_closure.py', 'instruction_residual.py',
                 'check_closure_wave.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    stable = dict(inputs_sha256=pins, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
        checked_instruction_families=4, checked_state_families=4,
        new_instruction_families=4, new_state_families=0,
        baseline_instruction_remaining=len(remaining), previous_instruction_families=len(prior),
        instruction_remaining=len(remaining)-len(prior)-4)
    old = json.loads(report.read_text()) if report.exists() else None
    protected = {p: sha(p) for p in (report, inv) if p.exists()}
    if old and any(old[key] != value for key, value in stable.items()):
        raise ValueError('Frozen finite-tail report differs from replay inputs')
    if old and (not inv.exists() or sha(inv) != stable['inventory_sha256']):
        raise ValueError('Frozen finite-tail inventory differs')
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           timeout=args.timeout, check=True)
        timings[str(path.relative_to(BUILD))] = round(time.monotonic()-started, 3)
        print('Compiled ' + str(path.relative_to(BUILD)), flush=True)
    receipt, log = kernel.fresh_paths(build, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory'], [paths[-1]], loadpaths, receipt, log,
                         recursive=True, timeout=args.audit_timeout)
    if NS + '.Regression' not in audit['checked_modules']:
        raise ValueError('Kernel audit omitted the regression controls')
    if any(sha(ROOT / name) != expected for name, expected in {**pins, **sources}.items()):
        raise ValueError('Proof input or source changed during replay')
    if any(sha(p) != expected for p, expected in protected.items()):
        raise ValueError('Published finite-tail evidence changed during replay')
    current = dict(stable, scope='Four exact both-bound census families; every completion covered.',
        kernel_audit='Full recursive coqchk, including regressions; no skipped dependencies.',
        compile_seconds=timings, audit_seconds=round(time.monotonic()-started, 3),
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        checked_modules=len(audit['checked_modules']), reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in paths})
    if old is None:
        exact(inv, inventory)
        exact(report, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (build / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print(f'Four new instruction tails fully kernel-audited; {stable["instruction_remaining"]} '
          'remain in the frozen hard cohort.', flush=True)


if __name__ == '__main__':
    main()
