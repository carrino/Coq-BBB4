"""Replay six reflected/relabeled state-exchange counter families.

Run check_burn4_ternary_counter.py and check_burn4_ternary_template.py first.
A sentinel protects an arbitrary dormant left suffix. Concrete entries take
one to eight steps; six-instruction recurrence and tail exclusion are proved
for all future steps. Undefined cells are covered through the completion theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
from generate_pipeline_examples import codes
import kernel_audit_cache_v3

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn4-ternary-swapped/proof'
TEMPLATE = ROOT / 'build/burn4-ternary-template/proof'
GENERIC = ROOT / 'build/burn4-ternary-counter/proof'
PREFIX = ROOT / 'research/burn4-ternary-swapped'
NAMESPACE = 'BBB24Burn4TernarySwapped'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, content):
    if path.exists() and path.read_text() != content:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(content)


def board_source(rows):
    out = '''From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout CertifiedBoard Symmetry Mirror CycleCensus Shadow ReadySwap.
From BBB24Burn4Ternary Require Import Counter.
From BBB24Burn4TernaryTemplate Require Import Template.
From BBB24Burn4TernarySwapped Require Import Swapped.
Import ListNotations.
'''
    for i, row in enumerate(rows):
        machine = row['machine']
        codes(machine)
        flat = machine.replace('_', '')
        branches = []
        for t in range(8):
            cell = flat[3*t:3*t+3]
            value = 'None' if cell == '---' else f'Some(mkTrans S{cell[0]} D{cell[1]} St{cell[2]})'
            branches.append(f'|St{chr(65+t//4)},S{t%4}=>{value}')
        out += f'Definition family{i}:TM:=fun q h=>match q,h with ' + ''.join(branches) + ' end.\n'
        suffix = '[' + ';'.join('S' + str(s) for s in row['dormant_left_suffix']) + ']'
        entry, start = row['entry_step'], row['counter_n']
        permutation = 'P' + ''.join(str(s) for s in row['symbol_map'][1:])
        out += f'''Definition normalized{i}:TM:=perm_tm(inverse_perm {permutation})(mirror_tm family{i}).
Lemma agrees{i}:tt_agrees(swap_tm normalized{i}).
Proof. intros q h H;destruct q,h;try reflexivity;destruct H as[H|[H|H]];discriminate. Qed.
Lemma entered{i}:csteps normalized{i} {entry} c0=Some(ready_swap_cconf(tc_after {start} {suffix} [])).
Proof. reflexivity. Qed.
Lemma family{i}_sound:NonHalt family{i} /\\ Bounds 0%N 8%N family{i}.
Proof.
 split.
 - apply mirror_nonhalt;apply(perm_nonhalt(inverse_perm {permutation})).
   exact(ts_nonhalt normalized{i} {suffix} {entry} {start} agrees{i} entered{i}).
 - apply mirror_bounds;apply(perm_bounds(inverse_perm {permutation})).
   eapply(bounds_weaken 0%N (N.of_nat {entry}) 0%N 8%N);try (vm_compute;discriminate).
   exact(ts_bounds normalized{i} {suffix} {entry} {start} agrees{i} entered{i}).
Qed.
'''
    out += 'Definition board:list TM:=[' + ';'.join('family' + str(i) for i in range(len(rows))) + '].\n'
    out += '''Lemma small_sound:BoardSound 0%N 8%N board.
Proof.
 intros f Hin tm Hle;unfold board in Hin;cbn in Hin.
'''
    for i in range(len(rows)):
        out += f' destruct Hin as[H{i}|Hin];[subst f;destruct family{i}_sound as[Hnh Hb];eapply extend_bounds;eauto|].\n'
    out += ''' contradiction.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 8%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound f Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall f,In f board->bootstrap_pending f.
Proof.
 intros f Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=f)in H;assumption.
Qed.
Print Assumptions small_sound.
'''
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        parser.error('Replay budgets must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path, report_path, inventory_path = [artifact(s) for s in ('input.json', 'checked.json', 'machines.json')]
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    protected = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    data = json.loads(input_path.read_text())
    rows = data['rows']
    if (len(rows) != 6 or len({row['machine'] for row in rows}) != 6
            or data['state_bound'] != 0 or data['instruction_bound'] != 8):
        raise ValueError('Expected six distinct swapped ternary families')
    for row in rows:
        codes(row['machine'])
        if (type(row['entry_step']) is not int or not 0 <= row['entry_step'] <= 8
                or type(row['counter_n']) is not int or row['counter_n'] < 0
                or any(type(s) is not int or not 0 <= s < 4 for s in row['dormant_left_suffix'])):
            raise ValueError('Invalid phase-entry parameters')
    template = PREFIX / 'Swapped.v'
    template_pins = {str(template.relative_to(ROOT)): sha(template)}
    if template_pins != data['template_sha256']:
        raise ValueError('Frozen theorem template differs')
    for name in ('Counter.v', 'Tail.v'):
        source = ROOT / 'research/burn4-ternary-counter' / name
        if sha(source) != sha(GENERIC / name):
            raise ValueError('Frozen counter dependency differs; replay its package first')
        template_pins[str(source.relative_to(ROOT))] = sha(source)
    source = ROOT / 'research/burn4-ternary-template/Template.v'
    if sha(source) != sha(TEMPLATE / 'Template.v'):
        raise ValueError('Frozen template dependency differs; replay its package first')
    template_pins[str(source.relative_to(ROOT))] = sha(source)
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (GENERIC, 'BBB24Burn4Ternary'), (TEMPLATE, 'BBB24Burn4TernaryTemplate'), (OUTPUT, NAMESPACE)]
    flags = [part for directory, namespace in load_paths for part in ('-Q', str(directory), namespace)]
    paths = [OUTPUT / 'Swapped.v', OUTPUT / 'Board.v']
    exact(paths[0], template.read_text())
    exact(paths[1], board_source(rows))
    descriptor = {'id': 'burn4_ternary_swapped', 'scope': 'both', 'rows': 6,
        'state_bound': 0, 'instruction_bound': 8, 'module': NAMESPACE + '.Inventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(GENERIC.relative_to(ROOT)), 'namespace': 'BBB24Burn4Ternary'},
                       {'path': str(TEMPLATE.relative_to(ROOT)), 'namespace': 'BBB24Burn4TernaryTemplate'},
                       {'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NAMESPACE + '.Board',
                                  'machines': [row['machine'] for row in rows]}))
    paths.append(path)
    sources = dependency_hashes(paths, flags)
    for name in ('check_burn4_ternary_swapped.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'template_sha256': template_pins, 'source_sha256': sources,
        'descriptor': descriptor, 'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
        'checked_state_families': 6, 'checked_instruction_families': 6,
        'template_theorem': NAMESPACE + '.Swapped.ts_bounds',
        'recurrence_theorem': NAMESPACE + '.Swapped.ts_recurrent'}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen replay evidence differs')
    if previous and (not inventory_path.exists() or sha(inventory_path) != stable['inventory_sha256']):
        raise ValueError('Frozen inventory differs')
    timings = {}
    for path in paths:
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           timeout=args.timeout, check=True)
        timings[path.stem] = round(time.monotonic() - start, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache_v3.fresh_paths(OUTPUT, 'kernel-audit')
    start = time.monotonic()
    audit = kernel_audit_cache_v3.audit([NAMESPACE + '.Inventory'], [paths[-1]], load_paths,
                                      receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **template_pins, **sources}.items()):
        raise ValueError('Frozen input, template or dependency changed during replay')
    if any(sha(path) != digest for path, digest in protected.items()):
        raise ValueError('Published evidence changed during replay')
    current = {**stable, 'scope': 'Exact state and instruction census bounds; all completions covered.',
        'compile_seconds': timings, 'audit_seconds': round(time.monotonic() - start, 3),
        'kernel_receipt': str(receipt.relative_to(ROOT)), 'kernel_receipt_sha256': sha(receipt),
        'kernel_audit': 'Full recursive coqchk.',
        'object_sha256': {str(path.with_suffix('.vo').relative_to(ROOT)): sha(path.with_suffix('.vo')) for path in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Six swapped ternary families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
