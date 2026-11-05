"""Rebuild both instruction upgrades of the shared S004/S005 counter.

The original state sources are reconstructed unchanged. New proofs establish
all eight instruction recurrences uniformly in the B2 write parameter. Every
replay checks the exact census inventory and all completions, then performs a
full recursive stock coqchk including old and new regression controls.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time

from check_campaign import ROOT, dependency_hashes, inventory_source, packed, sha
from instruction_residual import residual
import kernel_audit_cache_v3 as kernel

NAME = 'instruction-unary-pair'
NS = 'BBB24InstructionUnaryPair'
OLD_NS = 'BBB24Burn23S004S005Unary'
MACHINES = ('1LB0LA1LB1RB_3RB3RA0RB2LA', '1LB0LA1LB1RB_3RB3RA2RB2LA')


def artifact(suffix):
    return ROOT / 'research' / (NAME + '-' + suffix)


def exact(path, content):
    if path.exists() and path.read_text() != content:
        raise ValueError('Frozen artifact differs: ' + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        path.write_text(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    target = 64 * 1024**2
    if hard != resource.RLIM_INFINITY and hard < target:
        raise ValueError('Replay requires a 64 MiB stack limit')
    if soft != resource.RLIM_INFINITY and soft < target:
        resource.setrlimit(resource.RLIMIT_STACK, (target, hard))
    inp, report, inv = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    expected_rows = [dict(id='tr24-' + str(packed(m)), machine=m, code=packed(m)) for m in MACHINES]
    if data['rows'] != expected_rows or (data['state_bound'], data['instruction_bound']) != (0, 0):
        raise ValueError('Unexpected unary-pair families or bounds')
    remaining, pins = residual(ROOT / data['baseline_report'], data['baseline_sha256'])
    if not set(MACHINES) <= remaining:
        raise ValueError('Unary-pair family is outside the frozen historical cohort')
    pins[str(inp.relative_to(ROOT))] = sha(inp)
    old_input = ROOT / data['original_input']
    if sha(old_input) != data['original_input_sha256']:
        raise ValueError('Original state proof input differs')
    original = json.loads(old_input.read_text())
    if [r['machine'] for r in original['rows']] != list(MACHINES):
        raise ValueError('Original state inventory differs')
    pins[str(old_input.relative_to(ROOT))] = sha(old_input)
    build = ROOT / 'build' / NAME
    old, proof = build / 'state-source', build / 'proof'
    paths = []
    for directory, names, source_pins in (
        (old, ('UnaryPhases.v', 'Regression.v'), data['original_sources_sha256']),
        (proof, ('UnaryInstructions.v', 'Regression.v', 'Board.v'), data['templates_sha256'])):
        for name in names:
            relative = ('proof-sources/burn23-s004-s005-unary/' if directory == old
                        else 'proof-sources/' + NAME + '/') + name
            source = ROOT / relative
            if sha(source) != source_pins[relative]:
                raise ValueError('Frozen proof source differs: ' + relative)
            if directory == old and original['template_sha256'][relative] != sha(source):
                raise ValueError('Original state source pin differs: ' + relative)
            pins[relative] = sha(source)
            target = directory / name
            exact(target, source.read_text())
            paths.append(target)
    descriptor = dict(id='instruction_unary_pair', scope='both', rows=2,
        module=NS + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        was_pending='was_pending', state_bound=0, instruction_bound=0,
        exact_inventory_theorem=NS + '.Inventory.inventory_exact',
        proof_source=str((proof / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(inv.relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(old.relative_to(ROOT)), namespace=OLD_NS),
                    dict(path=str(proof.relative_to(ROOT)), namespace=NS)])
    path = proof / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NS + '.Board', 'machines': list(MACHINES)}) +
          '\nRequire Import ' + NS + '.Regression ' + OLD_NS + '.Regression.\n')
    paths.append(path)
    path = proof / 'Assumptions.v'
    exact(path, 'From ' + NS + ' Require Import Inventory UnaryInstructions.\n'
          'Print Assumptions UnaryInstructions.pu_instruction_zero.\n'
          'Print Assumptions Inventory.sound.\n')
    paths.append(path)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (old, OLD_NS), (proof, NS)]
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    sources = dependency_hashes(paths, flags)
    for name in ('check_instruction_unary_pair.py', 'instruction_residual.py', 'check_campaign.py',
                 'check_shadow_links.py', 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps(dict(rows=[dict(machine=m) for m in MACHINES]), indent=2) + '\n'
    stable = dict(inputs_sha256=pins, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
        checked_instruction_families=2, checked_state_families=2,
        new_instruction_families=2, new_state_families=0)
    previous = json.loads(report.read_text()) if report.exists() else None
    protected = {p: sha(p) for p in (report, inv) if p.exists()}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen unary-pair report differs from replay inputs')
    if previous and (not inv.exists() or sha(inv) != stable['inventory_sha256']):
        raise ValueError('Frozen unary-pair inventory differs')
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[str(path.relative_to(build))] = round(time.monotonic()-started, 3)
        print('Compiled ' + str(path.relative_to(build)), flush=True)
    assumptions = sorted(set(re.findall(r'(?m)^([A-Za-z_][A-Za-z_0-9.]*)\s*\n\s*:',
                                       paths[-1].with_suffix('.log').read_text())))
    if assumptions != ['FunctionalExtensionality.functional_extensionality_dep']:
        raise ValueError('Unexpected assumptions: ' + str(assumptions))
    receipt, log = kernel.fresh_paths(build, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory', NS + '.Assumptions'], paths[-2:], loadpaths,
                         receipt, log, recursive=True, timeout=args.audit_timeout)
    if not {NS + '.Regression', OLD_NS + '.Regression'} <= set(audit['checked_modules']):
        raise ValueError('Kernel audit omitted regression controls')
    if any(sha(ROOT / name) != expected for name, expected in {**pins, **sources}.items()):
        raise ValueError('Proof source or input changed during replay')
    if any(sha(p) != expected for p, expected in protected.items()):
        raise ValueError('Published evidence changed during replay')
    current = dict(stable, scope='Two exact both-bound census families; every completion covered.',
        actual_assumptions=assumptions, kernel_audit='Full recursive stock coqchk; no skipped dependencies.',
        compile_seconds=timings, audit_seconds=round(time.monotonic()-started, 3),
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        kernel_log_sha256=sha(log), checked_modules=len(audit['checked_modules']),
        reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in paths})
    if previous is None:
        exact(inv, inventory)
        exact(report, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (build / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Two unary-pair instruction families fully kernel-audited.', flush=True)


if __name__ == '__main__':
    main()
