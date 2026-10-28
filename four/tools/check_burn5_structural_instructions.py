"""Replay twenty fresh instruction transports from compact source certificates.

The ten ordinary sources are reconstructed in an isolated namespace. The one
handwritten paired-tail source is imported from its frozen replay package.
Every prefix equality, table inclusion, budget, completion and census inventory
is checked in Coq, followed by a full recursive audit. Discovery is not needed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time

import check_closure_wave as closure
import check_conjugate_batch as conjugate
from check_campaign import dependency_hashes, inventory_source
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build/burn5-structural-instruction/proof'
TAIL = ROOT / 'build/burn3-tail-invariant/proof'
PREFIX = ROOT / 'research/burn5-structural-instruction'
NS = 'BBB24Burn5StructuralInstruction'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def validate(data):
    if data['source_bound'] != 4096 or data['output_bound'] != 8192:
        raise ValueError('Unexpected transport budget')
    rows = data['source_certificates']
    if len(rows) != 10 or len({r['machine'] for r in rows}) != 10:
        raise ValueError('Expected ten distinct ordinary source certificates')
    for row in rows:
        closure.validate_row(row)
        if row['bound'] != 4096:
            raise ValueError('Unexpected source certificate bound')
    if data['tail_source'] != '1LB2LA1RB3RB_3RA1RB3LA1RA':
        raise ValueError('Unexpected handwritten source')
    machines = [row['machine'] for row in rows] + [data['tail_source']]
    if len(data['rows']) != 20:
        raise ValueError('Expected twenty transport targets')
    conjugate.validate(data, machines, data)
    pins = dict(data['source_inputs_sha256'])
    pins[data['tail_dependency_report']] = data['tail_dependency_sha256']
    for name, digest in pins.items():
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT) or sha(path) != digest:
            raise ValueError('Frozen source dependency differs: ' + name)
    tail_report = json.loads((ROOT / data['tail_dependency_report']).read_text())
    for name, digest in tail_report['source_sha256'].items():
        if sha(ROOT / name) != digest:
            raise ValueError('Rebuild the frozen paired-tail dependency: ' + name)
    if not (TAIL / 'Closeout.vo').exists():
        raise ValueError('Replay check_burn3_tail_invariant.py first')
    return machines, pins


def generate(data):
    machines, pins = validate(data)
    paths, specs = [], []
    for index, row in enumerate(data['source_certificates']):
        name = f'Source{index:03d}'
        path = BUILD / (name + '.v')
        exact(path, closure.shard_source([row]))
        paths.append(path)
        specs.append(dict(module=NS + '.' + name, board='board', bound=4096,
                          nonhalt='nonhalt', small_sound='small_sound'))
    path = BUILD / 'TailSource.v'
    exact(path, '''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Closeout.
From BBB24Burn3Tail Require Import Closeout.
Definition board := BBB24Burn3Tail.Closeout.board.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof.
 intros family [<-|H]; [exact (proj1 BBB24Burn3Tail.Closeout.exact_bounds)|contradiction].
Qed.
Lemma small_sound : BoardSound 4096%N 4096%N board.
Proof.
 intros family Hin tm Hle. eapply (bounds_weaken 0%N 10%N 4096%N 4096%N).
 - vm_compute; discriminate.
 - vm_compute; discriminate.
 - exact (BBB24Burn3Tail.Closeout.small_sound family Hin tm Hle).
Qed.
''')
    paths.append(path)
    specs.append(dict(module=NS + '.TailSource', board='board', bound=4096,
                      nonhalt='nonhalt', small_sound='small_sound'))
    config = dict(source_bound=4096, output_bound=8192, sources=specs)
    with tempfile.TemporaryDirectory(dir=BUILD, prefix='generate-') as temp:
        for source in conjugate.generate(config, machines, data['rows'], Path(temp), NS):
            target = BUILD / source.name
            exact(target, source.read_text())
            paths.append(target)
    descriptor = dict(id='burn5_structural_instruction', scope='both', rows=20,
        module=NS + '.Inventory', board='board', sound='sound', small_sound='small_sound',
        was_pending='was_pending', state_bound=8192, instruction_bound=8192,
        exact_inventory_theorem=NS + '.Inventory.inventory_exact',
        proof_source=str((BUILD / 'Inventory.v').relative_to(ROOT)),
        inventories=[dict(path=str(artifact('machines.json').relative_to(ROOT)), format='rows')],
        load_paths=[dict(path=str(TAIL.relative_to(ROOT)), namespace='BBB24Burn3Tail'),
                    dict(path=str(BUILD.relative_to(ROOT)), namespace=NS)])
    path = BUILD / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module':NS + '.ConjugateAll',
                                 'machines':[row[0] for row in data['rows']]}))
    paths.append(path)
    return paths, descriptor, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        raise ValueError('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    BUILD.mkdir(parents=True, exist_ok=True)
    input_path = artifact('input.json')
    report_path, inventory_path = artifact('checked.json'), artifact('machines.json')
    protected = {p:sha(p) for p in (report_path, inventory_path) if p.exists()}
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    data = json.loads(input_path.read_text())
    paths, descriptor, inputs = generate(data)
    inputs[str(input_path.relative_to(ROOT))] = sha(input_path)
    loadpaths = [(ROOT / 'theories', 'BBB24'), (TAIL, 'BBB24Burn3Tail'), (BUILD, NS)]
    flags = [arg for path, namespace in loadpaths for arg in ('-Q', str(path), namespace)]
    sources = dependency_hashes(paths, flags)
    for module in sys.modules.values():
        name = getattr(module, '__file__', None)
        if name and Path(name).resolve().is_relative_to(ROOT / 'tools'):
            path = Path(name).resolve()
            sources[str(path.relative_to(ROOT))] = sha(path)
    sources[str(Path(__file__).resolve().relative_to(ROOT))] = sha(__file__)
    inventory = json.dumps({'rows':[{'machine':row[0]} for row in data['rows']]}, indent=2) + '\n'
    stable = dict(inputs_sha256=inputs, source_sha256=sources, descriptor=descriptor,
                  inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
                  checked_state_families=20, checked_instruction_families=20,
                  source_certificate_count=10, imported_handwritten_sources=1)
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen report differs from replay inputs')
    if previous and (not inventory_path.exists() or sha(inventory_path) != stable['inventory_sha256']):
        raise ValueError('Frozen exact target inventory differs')
    if args.generate_only:
        print(json.dumps(dict(generated_modules=len(paths), targets=20, proof_credit=False)))
        return
    timings = {}
    for path in paths:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - started, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel.fresh_paths(BUILD, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory'], [paths[-1]], loadpaths, receipt, log,
                         recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **sources}.items()):
        raise ValueError('Frozen input or source changed during replay')
    if any(sha(path) != digest for path, digest in protected.items()):
        raise ValueError('Published evidence changed during replay')
    current = {**stable, 'scope':'Exact both-bound census families; all completions covered.',
        'compile_seconds':timings, 'kernel_receipt':str(receipt.relative_to(ROOT)),
        'kernel_receipt_sha256':sha(receipt), 'kernel_audit':'Full recursive coqchk.',
        'audit_seconds':round(time.monotonic() - started, 3),
        'checked_modules':len(audit['checked_modules']), 'reused_modules':len(audit['reused_modules']),
        'object_sha256':{str(path.with_suffix('.vo').relative_to(ROOT)):sha(path.with_suffix('.vo'))
                         for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (BUILD / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Twenty instruction transports kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
