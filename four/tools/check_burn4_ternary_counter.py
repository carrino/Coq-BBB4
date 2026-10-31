"""Replay a concrete ternary counter and exact instruction score four.

A macro induction proves unbounded A0 returns with exact exponential gaps.
A sentinel invariant excludes B0/B3 after step four; five saved recurrence
witnesses close all other obligations. Published evidence remains frozen.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
import kernel_audit_cache
from weighted_codec_v2 import bundle_decode, unpack
from weighted_render_v4 import render

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn4-ternary-counter/proof'
PREFIX = ROOT / 'research/burn4-ternary-counter'
NAMESPACE = 'BBB24Burn4Ternary'
MACHINE = '1LB2LB3LB2RA_3RA1RA1LB1RB'
TARGETS = [1, 2, 3, 5, 6]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(contents)


def render_five(row):
    graph = row['graph']
    if (graph['machine'] != MACHINE or graph['mirror'] != 0
            or graph['n'] != 2 or graph['t'] != 4096):
        raise ValueError('Unexpected five-target graph')
    source = render(row).split('Definition family:TM:=', 1)[0]
    labels = ';'.join(f'(St{chr(65 + t // 4)},S{t % 4})' for t in TARGETS)
    return source + f'''From BBB24 Require Import InstructionPortfolio.
From {NAMESPACE} Require Import Counter.
Definition family:TM:=tc_tm.
Definition targets:list Instr:=[{labels}].
Lemma five_checked:wp_graph_check family 2 4096 nodes targets certificate=true.
Proof. vm_compute;reflexivity. Qed.
Theorem five_sound:NonHalt family /\\
 forall tg,In tg targets -> forall N,exists k,N<=k /\\ FiresAt family tg k.
Proof. exact(wp_graph_check_sound _ _ _ _ _ _ five_checked). Qed.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        parser.error('Replay budgets must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = artifact('input.json')
    report_path, inventory_path = artifact('checked.json'), artifact('machines.json')
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    frozen = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    data = json.loads(input_path.read_text())
    expected = {'machine': MACHINE, 'selected_rows': 1, 'state_bound': 0,
                'instruction_bound': 4, 'quiet_instructions': [[1, 0], [1, 3]],
                'quiet_from': 4, 'last_firing_instruction': [1, 3],
                'last_firing_configuration_step': 3, 'counter_entry_step': 11,
                'return_gap': '3^(n+2)-2',
                'targets': TARGETS}
    if any(data.get(key) != value for key, value in expected.items()):
        raise ValueError('Unexpected theorem input or bound')
    bundle = ROOT / data['bundle']['path']
    if (bundle.resolve() != artifact('certificates.json').resolve()
            or data['bundle']['rows'] != 1
            or bundle.stat().st_size != data['bundle']['bytes']
            or sha(bundle) != data['bundle']['sha256']):
        raise ValueError('Compact certificate bundle differs')
    rows = bundle_decode(bundle.read_text())
    if len(rows) != 1:
        raise ValueError('Expected one certificate')
    row = unpack(rows[0])
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in (input_path, bundle)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [item for directory, namespace in load_paths for item in ('-Q', str(directory), namespace)]
    paths = []
    for name in ('Counter', 'Tail', 'FiveTargets', 'Closeout'):
        path = OUTPUT / (name + '.v')
        if name == 'FiveTargets':
            source = render_five(row)
        else:
            template = PREFIX / (name + '.v')
            inputs[str(template.relative_to(ROOT))] = sha(template)
            source = template.read_text()
        exact(path, source)
        paths.append(path)
    descriptor = {'id': 'burn4_ternary_counter', 'scope': 'both', 'rows': 1,
        'state_bound': 0, 'instruction_bound': 4,
        'module': NAMESPACE + '.Inventory', 'board': 'board',
        'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    inventory_source_path = OUTPUT / 'Inventory.v'
    exact(inventory_source_path, inventory_source({**descriptor,
          'module': NAMESPACE + '.Closeout', 'machines': [MACHINE]}))
    paths.append(inventory_source_path)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn4_ternary_counter.py', 'check_campaign.py',
                     'kernel_audit_cache.py', 'check_shadow_links.py',
                     'generate_pipeline_examples.py',
                     'weighted_codec_v2.py', 'weighted_render.py',
                     'weighted_render_v3.py', 'weighted_render_v4.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': MACHINE}]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources,
              'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_instruction_families': 1, 'checked_state_families': 1,
              'exact_instruction_score': 4,
              'return_gap_theorem': NAMESPACE + '.Counter.tc_gap_formula',
              'counter_recurrence_theorem': NAMESPACE + '.Counter.tc_A0_recurrent',
              'exact_score_theorem': NAMESPACE + '.Closeout.exact_instruction_score'}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen proof evidence differs')
    if previous and sha(inventory_path) != stable['inventory_sha256']:
        raise ValueError('Frozen inventory differs')
    timings = {}
    for path in paths:
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler',
                            'no', *flags, str(path)], stdout=log,
                           stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - start, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache.fresh_paths(OUTPUT, 'kernel-audit')
    kernel_audit_cache.audit([NAMESPACE + '.Inventory'], [paths[-1]], load_paths,
                            receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **sources}.items()):
        raise ValueError('Pinned sources or inputs changed during replay')
    if any(sha(path) != digest for path, digest in frozen.items()):
        raise ValueError('Published evidence changed during replay')
    current = {**stable,
        'scope': 'Exact state and instruction census bounds; all completions covered.',
        'compile_seconds': timings,
        'kernel_receipt': str(receipt.relative_to(ROOT)),
        'kernel_receipt_sha256': sha(receipt),
        'kernel_audit': 'Full recursive coqchk.',
        'object_sha256': {str(path.with_suffix('.vo').relative_to(ROOT)):
                         sha(path.with_suffix('.vo')) for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('One exact-score ternary-counter family kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
