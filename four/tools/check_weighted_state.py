"""Replay weighted state certificates and attach them to the census.

Each state selects one instruction whose recurrence is checked by WeightedState.
No instruction bound is inferred. Compact inputs suffice for a clean replay;
discovery graphs, LP software, and search executables are not needed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from check_campaign import dependency_hashes
from check_state_pipeline_batch import aggregate
from weighted_codec_v2 import bundle_decode, unpack
from weighted_render import HEADER as WEIGHTED_HEADER
from weighted_render_v4 import render as weighted_render

ROOT = Path(__file__).resolve().parents[1]
HEADER = WEIGHTED_HEADER + '''From Coq Require Import List NArith Lia.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard StateOnlyCloseout WeightedState.
Import ListNotations.
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_input(path):
    data = json.loads(path.read_text())
    rows = []
    inputs = {str(path.resolve().relative_to(ROOT)): sha(path)}
    for item in data['bundles']:
        bundle = ROOT/item['path']
        if sha(bundle) != item['sha256']:
            raise ValueError('Changed weighted state bundle')
        batch = bundle_decode(bundle.read_text())
        if len(batch) != item['rows']:
            raise ValueError('Changed weighted state bundle count')
        rows.extend(batch)
        inputs[item['path']] = item['sha256']
    if not rows or len(rows) != data['rows'] or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Empty, incomplete, or duplicate state inventory')
    for row in rows:
        choices = row['state_choices']
        if not isinstance(choices, list) or len(choices) != 2 or any(type(s) is not int or not 0 <= s < 4 for s in choices):
            raise ValueError('Expected one valid symbol choice per state')
        unpack(row)
    return rows, inputs


def render_case(row):
    decoded = unpack(row)
    source = 'Definition nodes' + weighted_render(decoded).split('Definition nodes', 1)[1].split('Lemma checked:', 1)[0]
    choices = row['state_choices']
    graph = decoded['graph']
    source += f'''Definition state_choice q := match q with StA=>S{choices[0]} | StB=>S{choices[1]} end.
'''
    target = '(mirror_tm family)' if graph['mirror'] else 'family'
    source += fr'''Lemma state_checked :
  ws_graph_check 4096%N {target} {graph['n']}%nat {graph['t']}%nat
    nodes state_choice certificate = true.
Proof. vm_compute. reflexivity. Qed.
Theorem family_run : NonHalt family /\ QHBound (N.to_nat 4096%N) family.
Proof.
'''
    if graph['mirror']:
        source += '''  destruct (ws_graph_check_sound _ _ _ _ _ _ _ state_checked) as [Hnh Hb].
  split; [apply mirror_nonhalt; exact Hnh|].
  intros q n [Hv Hquiet]. apply (Hb q n). split.
  - apply mirror_visits; exact Hv.
  - intros k Hk Hvisit. apply (Hquiet k Hk). apply mirror_visits; exact Hvisit.
'''
    else:
        source += '  exact (ws_graph_check_sound _ _ _ _ _ _ _ state_checked).\n'
    source += '''Qed.
Theorem family_completions : forall tm, TM_le family tm -> QHBound (N.to_nat 4096%N) tm.
Proof. intros tm Hle. destruct family_run as [Hnh Hb]. eapply state_bound_extend; eauto. Qed.
'''
    return source


def render_shard(rows):
    names = [f'Case{i:04}' for i in range(len(rows))]
    source = HEADER
    for name, row in zip(names, rows):
        source += f'Module {name}.\n'+render_case(row)+f'End {name}.\n'
    source += 'Definition board := ['+';'.join(name+'.family' for name in names)+'].\n'
    source += '''Theorem board_state_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. intros family Hin. unfold board in Hin; cbn in Hin.
'''
    source += ''.join(f'  destruct Hin as [<-|Hin]; [exact {name}.family_completions|].\n' for name in names)
    source += '''  contradiction.
Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem board_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound.
  pose proof pending_checked as H. apply forallb_forall with (x:=family) in H; assumption.
Qed.
'''
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--namespace', default='BBB24WeightedState')
    parser.add_argument('--timeout', type=int, default=1800)
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.namespace):
        raise ValueError('Invalid logical namespace')
    args.output_dir = args.output_dir.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows, inputs = load_input(args.input)
    flags = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(args.output_dir), args.namespace]
    modules, paths = [], []
    for offset in range(0, len(rows), 16):
        name = f'WeightedState{len(modules):04}'
        path = args.output_dir/(name+'.v')
        path.write_text(render_shard(rows[offset:offset+16]))
        modules.append(name); paths.append(path)
    path = args.output_dir/'WeightedStateAll.v'
    path.write_text(aggregate(modules, len(rows), 4096, args.namespace))
    paths.append(path)
    dependencies = dependency_hashes(paths, flags)
    sources = {**dependencies, **{'tools/'+name: sha(ROOT/'tools'/name) for name in (
        'check_weighted_state.py', 'check_campaign.py', 'check_state_pipeline_batch.py',
        'weighted_codec_v2.py', 'weighted_render.py', 'weighted_render_v3.py', 'weighted_render_v4.py')}}
    compiler = subprocess.check_output(['coqc', '--version'], text=True)
    evidence = {'inputs': inputs, 'source_sha256': sources, 'coq_version': compiler}
    if not args.refresh:
        previous = json.loads(args.report.read_text())
        if any(previous[key] != value for key, value in evidence.items()):
            raise ValueError('Recorded state proof inputs changed')
    for path in paths:
        current = {'source': sha(path), 'dependencies': dependency_hashes([path], flags), 'coq_version': compiler}
        receipt, vo = path.with_suffix('.checked.json'), path.with_suffix('.vo')
        if args.resume and receipt.exists() and vo.exists():
            previous = json.loads(receipt.read_text())
            if previous == {**current, 'vo_sha256': sha(vo)}:
                print('Reused '+path.stem, flush=True); continue
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        receipt.write_text(json.dumps({**current, 'vo_sha256': sha(vo)}, indent=2)+'\n')
        print(f'Checked {path.stem}: {time.monotonic()-start:.2f}s', flush=True)
    with (args.output_dir/'coqchk.log').open('w') as log:
        subprocess.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags,
                        args.namespace+'.WeightedStateAll'], stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=max(args.timeout, 120*len(rows)))
    if inputs != load_input(args.input)[1] or any(sha(ROOT/name) != digest for name, digest in sources.items()):
        raise ValueError('Inputs changed during state audit')
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]}, indent=2)+'\n'
    report = {**evidence, 'scope': 'State-only bounds and census discharge; no instruction claim.',
              'state_checked_families': len(rows), 'state_census_linked_families': len(rows),
              'instruction_checked_families': 0, 'state_bound': 4096,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'module': args.namespace+'.WeightedStateAll',
              'validation': 'VM recurrence and pending-membership proofs plus full recursive coqchk.',
              'descriptor': {'module': args.namespace+'.WeightedStateAll', 'board': 'state_board',
                             'small_sound': 'state_board_small', 'sound': 'state_board_bound',
                             'was_pending': 'state_board_pending',
                             'load_paths': [{'path': str(args.output_dir.relative_to(ROOT)), 'namespace': args.namespace}],
                             'machine_inputs': [{'path': str(args.inventory.resolve().relative_to(ROOT)), 'format': 'json_rows'}]}}
    serialized = json.dumps(report, indent=2, sort_keys=True)+'\n'
    if args.refresh:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(serialized)
        args.inventory.parent.mkdir(parents=True, exist_ok=True)
        args.inventory.write_text(inventory)
    elif args.report.read_text() != serialized or args.inventory.read_text() != inventory:
        raise ValueError('Replay differs from recorded state evidence')
    print(f'{len(rows)} weighted state families checked and census-linked.', flush=True)


if __name__ == '__main__':
    main()
