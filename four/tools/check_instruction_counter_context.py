"""Replay four exact transition bounds from one context-parametric counter proof.

The earlier TwosCounter source is reconstructed unchanged. Its arbitrary-context
block macro supports the new persistent-left-context phases. Every selected exact
family receives state bound zero and exact instruction score two. Original pending
membership, every completion and the exact inventory are checked in Coq; full
recursive stock coqchk includes the new regressions on every invocation.
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

PREFIX = ROOT / 'research/instruction-counter-context'
BUILD = ROOT / 'build/instruction-counter-context'
NS = 'BBB24CounterEntry'
MACHINES = ['1LB2LB3LB2RA_' + str(w) + 'RB3RA2LB1RA' for w in range(4)]


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))
    inp, report, inv = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    rows = [dict(id='tr24-' + str(packed(m)), machine=m, code=packed(m)) for m in MACHINES]
    if data['rows'] != rows or (data['state_bound'], data['instruction_bound']) != (0, 2):
        raise ValueError('Unexpected context-counter families or bounds')
    remaining, pins = residual(ROOT / data['baseline_report'], data['baseline_sha256'])
    if not set(MACHINES) <= remaining:
        raise ValueError('Context-counter family is outside the frozen instruction remainder')
    pins[str(inp.relative_to(ROOT))] = sha(inp)
    proof, old = BUILD / 'proof', BUILD / 'original-counter'
    paths = []
    for relative, expected in data['required_original_sources_sha256'].items():
        source = ROOT / relative
        if sha(source) != expected:
            raise ValueError('Original symbolic counter differs: ' + relative)
        pins[relative] = expected
        target = old / source.name
        exact(target, source.read_text());paths.append(target)
    if set(data['required_original_sources_sha256']) != {'proof-sources/instruction-sparse-twos/TwosCounter.v'}:
        raise ValueError('Unexpected original symbolic counter dependency')
    for name in ('ContextCounter.v', 'CounterEntry.v', 'Regression.v', 'Board.v'):
        source = ROOT / 'proof-sources/instruction-counter-context' / name
        expected = data['templates_sha256'][str(source.relative_to(ROOT))]
        if sha(source) != expected:
            raise ValueError('Frozen context-counter source differs: ' + str(source))
        pins[str(source.relative_to(ROOT))] = expected
        target = proof / name
        exact(target, source.read_text());paths.append(target)
    descriptor = dict(id='instruction_counter_context', scope='both', rows=4,
        module=NS + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        was_pending='was_pending', state_bound=0, instruction_bound=2,
        exact_inventory_theorem=NS + '.Inventory.inventory_exact',
        proof_source=str((proof / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(inv.relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(old.relative_to(ROOT)), namespace='BBB24SparseTwos'),
                    dict(path=str(proof.relative_to(ROOT)), namespace=NS)])
    path = proof / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NS + '.Board', 'machines': MACHINES}) +
          '\nRequire Import ' + NS + '.Regression.\n')
    paths.append(path)
    assumptions = proof / 'Assumptions.v'
    exact(assumptions, 'From ' + NS + ' Require Import CounterEntry Inventory.\n' +
          'Print Assumptions CounterEntry.rb_instruction_attains.\n' +
          'Print Assumptions Inventory.sound.\n')
    paths.append(assumptions)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (old, 'BBB24SparseTwos'), (proof, NS)]
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    sources = dependency_hashes(paths, flags)
    for name in ('check_instruction_counter_context.py', 'instruction_residual.py', 'check_campaign.py',
                 'check_shadow_links.py', 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps(dict(rows=[dict(machine=m) for m in MACHINES]), indent=2) + '\n'
    stable = dict(inputs_sha256=pins, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
        checked_instruction_families=4, checked_state_families=4,
        new_instruction_families=4, new_state_families=0)
    previous = json.loads(report.read_text()) if report.exists() else None
    protected = {p: sha(p) for p in (report, inv) if p.exists()}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen context-counter report differs from replay inputs')
    if previous and (not inv.exists() or sha(inv) != stable['inventory_sha256']):
        raise ValueError('Frozen context-counter inventory differs')
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[str(path.relative_to(BUILD))] = round(time.monotonic()-started, 3)
        print('Compiled ' + str(path.relative_to(BUILD)), flush=True)
    actual_assumptions = sorted(set(re.findall(r'(?m)^([A-Za-z_][A-Za-z_0-9.]*)\s*\n\s*:',
                                               assumptions.with_suffix('.log').read_text())))
    if actual_assumptions != ['FunctionalExtensionality.functional_extensionality_dep']:
        raise ValueError('Unexpected proof assumptions: ' + str(actual_assumptions))
    receipt, log = kernel.fresh_paths(BUILD, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory', NS + '.Assumptions'], paths[-2:], loadpaths,
                         receipt, log, recursive=True, timeout=args.audit_timeout)
    if NS + '.Regression' not in audit['checked_modules']:
        raise ValueError('Kernel audit omitted context-counter regressions')
    if any(sha(ROOT / name) != expected for name, expected in {**pins, **sources}.items()):
        raise ValueError('Context-counter source or input changed during replay')
    if any(sha(p) != expected for p, expected in protected.items()):
        raise ValueError('Published context-counter evidence changed during replay')
    current = dict(stable, scope='Four exact both-bound census families; every completion covered.',
        kernel_audit='Full recursive coqchk including regressions; no skipped dependencies.',
        actual_assumptions=actual_assumptions, compile_seconds=timings,
        audit_seconds=round(time.monotonic()-started, 3),
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        checked_modules=len(audit['checked_modules']), reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in paths})
    if previous is None:
        exact(inv, inventory)
        exact(report, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (BUILD / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Four context-counter instruction families fully kernel-audited.', flush=True)


if __name__ == '__main__':
    main()
