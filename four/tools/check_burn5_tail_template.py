"""Replay21 paired-digit tail entries under seven fixed transitions.

Run check_burn3_tail_invariant.py first. The invariant protects any dormant left
suffix. Concrete entries are checked independently, including state exchange,
reflection and symbol relabeling. All completions and exact inventory are proved.
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
OUTPUT = ROOT / 'build/burn5-tail-template/proof'
GENERIC = ROOT / 'build/burn3-tail-invariant/proof'
PREFIX = ROOT / 'research/burn5-tail-template'
NAMESPACE = 'BBB24Burn5TailTemplate'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, content):
    if path.exists() and path.read_text() != content:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(content)


def syms(xs):
    return '[' + ';'.join('S' + str(s) for s in xs) + ']'


def configuration(row):
    q, left, head, right = row
    return f'(St{chr(65+q)},({syms(left)},S{head},{syms(right)}))'


def board_source(rows):
    out = """From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout CertifiedBoard Symmetry Mirror CycleCensus.
From BBB24Burn3Tail Require Import TailInvariant.
From BBB24Burn5TailTemplate Require Import Transfer.
Import ListNotations.
"""
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
        permutation = 'P' + ''.join(str(s) for s in row['symbol_map'][1:])
        actual = f'(mirror_tm family{i})' if row['mirror'] else f'family{i}'
        switched = 'true' if row['state_exchange'] else 'false'
        suffix = syms(row['dormant_left_suffix'])
        entry, anchor = row['destination_boot'], row['source_boot']
        out += f"""Definition normalized{i}:TM:=perm_tm(inverse_perm {permutation}){actual}.
Definition source{i}:cconf:={configuration(row['source_configuration'])}.
Lemma agrees{i}:tp_agrees(tp_tm {switched} normalized{i}).
Proof. intros q h H;destruct q,h;try reflexivity;exfalso;apply H;reflexivity. Qed.
Lemma source_entry{i}:csteps ti_tm {anchor} c0=Some source{i}.
Proof. vm_compute;reflexivity. Qed.
Lemma source_inv{i}:ti_inv source{i}.
Proof. eapply(tp_anchor_inv {anchor});[lia|exact source_entry{i}]. Qed.
Lemma entered{i}:tp_entry_check normalized{i} {entry} {switched} {suffix} source{i}=true.
Proof. vm_compute;reflexivity. Qed.
Lemma normalized{i}_sound:NonHalt normalized{i} /\\ Bounds 0%N 147%N normalized{i}.
Proof.
 split.
 - exact(tp_nonhalt normalized{i} {switched} {suffix} source{i} {entry} {anchor}
    agrees{i} source_entry{i} source_inv{i} entered{i}).
 - eapply(bounds_weaken 0%N(N.of_nat {entry})0%N 147%N);try(vm_compute;discriminate).
   exact(tp_bounds normalized{i} {switched} {suffix} source{i} {entry} {anchor}
    agrees{i} source_entry{i} source_inv{i} entered{i}).
Qed.
Lemma family{i}_sound:NonHalt family{i} /\\ Bounds 0%N 147%N family{i}.
Proof.
 destruct normalized{i}_sound as[Hnh Hb];unfold normalized{i} in Hnh,Hb.
 apply perm_nonhalt in Hnh;apply perm_bounds in Hb.
"""
        if row['mirror']:
            out += ' split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb].\n'
        else:
            out += ' split;assumption.\n'
        out += 'Qed.\n'
    out += 'Definition board:list TM:=[' + ';'.join('family' + str(i) for i in range(len(rows))) + '].\n'
    out += """Lemma small_sound:BoardSound 0%N 147%N board.
Proof.
 intros f Hin tm Hle;unfold board in Hin;cbn in Hin.
"""
    for i in range(len(rows)):
        out += f' destruct Hin as[H{i}|Hin];[subst f;destruct family{i}_sound as[Hnh Hb];eapply extend_bounds;eauto|].\n'
    out += """ contradiction.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 147%N scoreN scoreN tm).
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
"""
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
    if (len(rows) != 21 or len({row['machine'] for row in rows}) != 21
            or data['state_bound'] != 0 or data['instruction_bound'] != 147):
        raise ValueError('Expected21 distinct paired-digit tail families')
    for row in rows:
        codes(row['machine'])
        if (type(row['destination_boot']) is not int or not 0 <= row['destination_boot'] <= 147
                or type(row['source_boot']) is not int or row['source_boot'] < 10
                or sorted(row['symbol_map']) != [0, 1, 2, 3] or row['symbol_map'][0] != 0
                or type(row['mirror']) is not bool or type(row['state_exchange']) is not bool
                or any(type(s) is not int or not 0 <= s < 4 for s in row['dormant_left_suffix'])):
            raise ValueError('Invalid phase-entry parameters')
    template = PREFIX / 'Transfer.v'
    template_pins = {str(template.relative_to(ROOT)): sha(template)}
    if template_pins != data['template_sha256']:
        raise ValueError('Frozen theorem template differs')
    for name in ('TailInvariant.v', 'Closeout.v'):
        source = ROOT / 'research/burn3-tail-invariant' / name
        if sha(source) != sha(GENERIC / name):
            raise ValueError('Frozen counter dependency differs; replay its package first')
        template_pins[str(source.relative_to(ROOT))] = sha(source)
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (GENERIC, 'BBB24Burn3Tail'), (OUTPUT, NAMESPACE)]
    flags = [part for directory, namespace in load_paths for part in ('-Q', str(directory), namespace)]
    paths = [OUTPUT / 'Transfer.v', OUTPUT / 'Board.v']
    exact(paths[0], template.read_text())
    exact(paths[1], board_source(rows))
    descriptor = {'id': 'burn5_tail_template', 'scope': 'both', 'rows': 21,
        'state_bound': 0, 'instruction_bound': 147, 'module': NAMESPACE + '.Inventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound', 'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.Inventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(GENERIC.relative_to(ROOT)), 'namespace': 'BBB24Burn3Tail'},
                       {'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source({**descriptor, 'module': NAMESPACE + '.Board',
                                  'machines': [row['machine'] for row in rows]}))
    paths.append(path)
    sources = dependency_hashes(paths, flags)
    for name in ('check_burn5_tail_template.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'template_sha256': template_pins, 'source_sha256': sources,
        'descriptor': descriptor, 'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
        'checked_state_families': 21, 'checked_instruction_families': 21,
        'template_theorem': NAMESPACE + '.Transfer.tp_bounds',
        'recurrence_theorem': NAMESPACE + '.Transfer.tp_recurrent'}
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
    print('21 paired-digit tail families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
