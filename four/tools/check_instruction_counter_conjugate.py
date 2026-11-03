"""Replay the exact transient-A0 instruction score of a conjugate counter.

The old generic counter sources are rebuilt unchanged. Transport starts at the
proved nonblank boundary after three actual steps, rather than assuming that
the transformed source starts from a blank A configuration. Every completion,
original census membership, exact inventory, and both old/new regressions are
included in a fresh full recursive stock coqchk audit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
NS = 'BBB24CounterConjugate'
NAME = 'instruction-counter-conjugate'
MACHINE = '1LB2LB1LB3RA_2RA3LB3RA1RA'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=ROOT,
                        help='Shared four/ source root; defaults to this checkout')
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))
    shared = args.source_root.resolve()
    sys.path.insert(0, str(shared / 'tools'))
    from check_campaign import packed
    from instruction_residual import residual
    import kernel_audit_cache_v3 as kernel
    prefix = ROOT / 'research' / NAME
    inp, report, inventory = [prefix.with_name(NAME + '-' + suffix)
                              for suffix in ('input.json', 'checked.json', 'machines.json')]
    data = json.loads(inp.read_text())
    if (data['rows'] != [dict(machine=MACHINE, code=2819321740, id='tr24-2819321740')] or
            packed(MACHINE) != 2819321740 or
            (data['state_bound'], data['instruction_bound']) != (0, 1)):
        raise ValueError('Unexpected exact counter-conjugate inventory or bound')
    remaining, pins = residual(shared / data['baseline_report'], data['baseline_sha256'])
    if MACHINE not in remaining:
        raise ValueError('Conjugate family is outside the frozen instruction baseline')
    invtext = json.dumps(dict(rows=[dict(machine=MACHINE)]), indent=2) + '\n'
    if inventory.read_text() != invtext:
        raise ValueError('Frozen exact machine inventory differs')
    protected = {p: sha(p) for p in (inp, inventory, Path(__file__).resolve())}
    build = ROOT / 'build' / NAME
    old, proof = build / 'old-source', build / 'proof'
    files = []
    expected_old = {'proof-sources/instruction-sparse-twos/' + name
                    for name in ('TwosCounter.v', 'Regression.v')}
    if set(data['original_sources_sha256']) != expected_old:
        raise ValueError('Unexpected original-source manifest')
    for relative, expected in data['original_sources_sha256'].items():
        source = shared / relative
        if sha(source) != expected:
            raise ValueError('Original counter source differs: ' + relative)
        protected[source] = expected
    for name in ('TwosCounter.v', 'Regression.v'):
        source = shared / 'proof-sources/instruction-sparse-twos' / name
        target = old / name
        exact(target, source.read_text()); files.append(target)
    names = ('ConjugateCounter.v', 'Board.v', 'Regression.v', 'Inventory.v')
    expected_new = {'proof-sources/' + NAME + '/' + name for name in names}
    if set(data['templates_sha256']) != expected_new:
        raise ValueError('Unexpected proof template manifest')
    for name in names:
        relative = 'proof-sources/' + NAME + '/' + name
        source = ROOT / relative
        if sha(source) != data['templates_sha256'][relative]:
            raise ValueError('Frozen conjugate proof differs: ' + relative)
        protected[source] = sha(source)
        target = proof / name
        exact(target, source.read_text()); files.append(target)
    assumptions = proof / 'Assumptions.v'
    exact(assumptions, '''From BBB24CounterConjugate Require Import Inventory ConjugateCounter.
Require Import BBB24SparseTwos.Regression.
Set Printing All.
Print Assumptions ConjugateCounter.instruction_attains.
Print Assumptions Inventory.sound.
''')
    files.append(assumptions)
    loadpaths = [(shared / 'theories', 'BBB24'), (old, 'BBB24SparseTwos'), (proof, NS)]
    flags = [arg for directory, namespace in loadpaths for arg in ('-Q', str(directory), namespace)]
    timings = {}
    for path in files:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-q', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[str(path.relative_to(build))] = round(time.monotonic() - started, 3)
        print('Compiled ' + str(path.relative_to(build)), flush=True)
    actual_assumptions = sorted(set(re.findall(r'(?m)^([A-Za-z_][A-Za-z_0-9.]*)\s*\n\s*:',
                                               assumptions.with_suffix('.log').read_text())))
    if actual_assumptions != ['FunctionalExtensionality.functional_extensionality_dep']:
        raise ValueError('Unexpected printed assumptions: ' + str(actual_assumptions))
    descriptor = dict(id='instruction_counter_conjugate', scope='both', rows=1,
        state_bound=0, instruction_bound=1, module=NS+'.Inventory', board='board',
        sound='sound', small_sound='small_sound', was_pending='was_pending',
        proof_source='build/'+NAME+'/proof/Inventory.v',
        exact_inventory_theorem=NS+'.Inventory.inventory_exact',
        inventories=[dict(path='research/'+NAME+'-machines.json', format='rows')],
        load_paths=[dict(path=str(p.relative_to(ROOT)), namespace=ns) for p, ns in loadpaths[1:]])
    snapshot = kernel.snapshot(files, loadpaths)
    sources = {}
    for item in snapshot['graph'].values():
        path = Path(item['source'])
        if path.is_relative_to(ROOT):
            sources[str(path.relative_to(ROOT))] = item['source_sha256']
        elif path.is_relative_to(shared):
            sources[str(path.relative_to(shared))] = item['source_sha256']
    sources['tools/check_instruction_counter_conjugate.py'] = sha(__file__)
    for name in ('check_campaign.py', 'instruction_residual.py', 'kernel_audit_cache_v3.py'):
        relative = 'tools/' + name
        sources[relative] = sha(shared / relative)
        protected[shared / relative] = sources[relative]
    inputs = {**pins, 'research/'+NAME+'-input.json': sha(inp),
              **data['original_sources_sha256'], **data['templates_sha256']}
    stable = dict(inputs_sha256=inputs, source_sha256=sources, descriptor=descriptor,
        inventory_sha256=sha(inventory), checked_instruction_families=1, checked_state_families=1,
        new_instruction_families=1, new_state_families=0, actual_assumptions=actual_assumptions,
        exact_instruction_score=1, last_instruction_index=0)
    previous = json.loads(report.read_text()) if report.exists() else None
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen counter-conjugate report differs from replay inputs')
    if previous:
        protected[report] = sha(report)
    receipt, log = kernel.fresh_paths(build, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS+'.Inventory', NS+'.Assumptions'], [files[-2], files[-1]],
                         loadpaths, receipt, log, recursive=True, timeout=args.audit_timeout)
    required = {NS+'.Regression', 'BBB24SparseTwos.Regression'}
    if not required <= set(audit['checked_modules']):
        raise ValueError('Kernel audit omitted required regression controls')
    if any(sha(p) != expected for p, expected in protected.items()):
        raise ValueError('Frozen source or input changed during proof replay')
    result = dict(stable, scope='One exact conjugate-counter instruction family; every completion covered.',
        compile_seconds=timings, audit_seconds=round(time.monotonic()-started, 3),
        kernel_audit='Full recursive stock coqchk, including old and new regression modules.',
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        kernel_log_sha256=sha(log), checked_modules=len(audit['checked_modules']),
        reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in files})
    if previous is None:
        exact(report, json.dumps(result, indent=2, sort_keys=True) + '\n')
    (build/'current-proof-receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('Conjugate counter exact instruction score 1: full recursive kernel audit passed.', flush=True)


if __name__ == '__main__':
    main()
