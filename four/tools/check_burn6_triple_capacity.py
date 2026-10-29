"""Replay a bilateral triple-window capacity invariant and eight recurrence proofs.

The new boundary invariant supplies the hypothesis needed by the existing
binary-ranking checker. Every instruction recurs, giving both bounds zero.
All generated objects stay under build; published evidence remains frozen.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
import kernel_audit_cache_v3 as kernel_audit_cache
from weighted_codec_v2 import bundle_decode, unpack
from weighted_render_v4 import render
from weighted_render import naturals

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn6-triple-capacity/proof'
PREFIX = ROOT / 'research/burn6-triple-capacity'
NAMESPACE = 'BBB24Burn6TripleCapacity'
MACHINE = '1LB1RB1RA2LA_3RA0RA3RA3LB'
TARGETS = [0, 1, 3, 4, 5, 6, 7]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(contents)


def render_graph(row, capacity):
    graph = row['graph']
    if (graph['machine'] != MACHINE or graph['mirror'] != 1
            or graph['n'] != 2 or graph['t'] != 4096):
        raise ValueError('Unexpected recurrence graph')
    weights = capacity['weights']
    if (capacity['scale'] != 1 or len(weights) != 172
            or any(type(x) is not int or x < 0 for x in weights)
            or [(i, x) for i, x in enumerate(weights) if x]
            != [(32, 2), (33, 3), (69, 2), (115, 1), (131, 1)]
            or len(capacity['bias']) != len(graph['nodes'])):
        raise ValueError('Unexpected triple-capacity certificate')
    source = render(row).split('Lemma checked:', 1)[0]
    labels = ';'.join(f'(St{chr(65 + t // 4)},S{t % 4})' for t in TARGETS)
    return source + f'''From BBB24 Require Import InstructionPortfolio.
From {NAMESPACE} Require Import TripleCapacity.
Definition left_score(a b c:Sym):nat:=match a,b,c with
 |S1,S2,S1=>2|_,_,_=>0 end.
Definition right_score(a b c:Sym):nat:=
 (match a,b with S1,S0=>2|S1,S1=>3|_,_=>0 end)+
 (match a,b,c with S0,S1,S3=>1|S1,S1,S3=>1|_,_,_=>0 end).
Definition capacity:TCapacity:=mkTCapacity 1 [] left_score right_score
 (wc_table 0%nat nodes {naturals(capacity['bias'])}).
Definition actual:=mirror_tm family.
Definition targets:list Instr:=[{labels}].
Lemma seven_checked:wp_graph_check actual 2 4096 nodes targets certificate=true.
Proof. vm_compute;reflexivity. Qed.
Lemma eighth_checked:tc_graph_check actual 2 4096 nodes (StA,S2) capacity(wc_components target_2)=true.
Proof. vm_compute;reflexivity. Qed.
Theorem seven_sound:NonHalt actual /\\
 forall tg,In tg targets -> forall N,exists k,N<=k /\\ FiresAt actual tg k.
Proof. exact(wp_graph_check_sound _ _ _ _ _ _ seven_checked). Qed.
Theorem eighth_sound:NonHalt actual /\\
 forall N,exists k,N<=k /\\ FiresAt actual(StA,S2)k.
Proof. exact(tc_graph_check_sound _ _ _ _ _ _ _ eighth_checked). Qed.
Print Assumptions eighth_sound.
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
                'instruction_bound': 0, 'triple_target': [0, 2], 'mirror': 1,
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
    load_paths = [(ROOT / 'theories', 'BBB24'),
                  (ROOT / 'build/burn3-frequent-invariants/proof', 'BBB24Burn3Pair'),
                  (OUTPUT, NAMESPACE)]
    flags = [item for directory, namespace in load_paths for item in ('-Q', str(directory), namespace)]
    paths = []
    for name in ('TripleCapacity', 'GraphCertificate', 'Regression', 'Closeout'):
        path = OUTPUT / (name + '.v')
        if name == 'GraphCertificate':
            source = render_graph(row, rows[0]['triple_capacity'])
        else:
            template = PREFIX / (name + '.v')
            inputs[str(template.relative_to(ROOT))] = sha(template)
            source = template.read_text()
        exact(path, source)
        paths.append(path)
    descriptor = {'id': 'burn6_triple_capacity', 'scope': 'both', 'rows': 1,
        'state_bound': 0, 'instruction_bound': 0,
        'module': NAMESPACE + '.Inventory', 'board': 'board',
        'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': 'build/burn3-frequent-invariants/proof', 'namespace': 'BBB24Burn3Pair'},
                       {'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    inventory_source_path = OUTPUT / 'Inventory.v'
    exact(inventory_source_path, inventory_source({**descriptor,
          'module': NAMESPACE + '.Closeout', 'machines': [MACHINE]}))
    paths.append(inventory_source_path)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn6_triple_capacity.py', 'check_campaign.py',
                     'kernel_audit_cache.py', 'kernel_audit_cache_v3.py', 'check_shadow_links.py',
                     'generate_pipeline_examples.py',
                     'weighted_codec_v2.py', 'weighted_render.py',
                     'weighted_render_v3.py', 'weighted_render_v4.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': MACHINE}]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources,
              'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_instruction_families': 1, 'checked_state_families': 1,
              'all_recurrent_theorem': NAMESPACE + '.Closeout.all_instructions_recur'}
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
    audit_started = time.monotonic()
    audit_result = kernel_audit_cache.audit([NAMESPACE + '.Inventory'], [paths[-1]], load_paths,
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
        'audit_seconds': round(time.monotonic() - audit_started, 3),
        'checked_modules': len(audit_result['checked_modules']),
        'reused_modules': len(audit_result['reused_modules']),
        'object_sha256': {str(path.with_suffix('.vo').relative_to(ROOT)):
                         sha(path.with_suffix('.vo')) for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('One triple-capacity recurrence family kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
