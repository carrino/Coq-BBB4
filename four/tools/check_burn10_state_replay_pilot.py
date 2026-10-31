"""Bounded state replay of four previously unreplayed rows per cheap stage.

Generated Coq files stay ignored. Checker and census-membership modules are
timed separately. Existing core proof objects are imported, never rebuilt.
Only a successful full recursive audit permits a checked report.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import subprocess
import time

from check_campaign import inventory_source, packed, forall_proof
from check_closure_wave import certificate
from check_shadow_links import dependency_hashes
from generate_pipeline_examples import codes
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/burn10-state-closeout/replay-pilot'
NAMESPACE = 'BBB24Burn10StateReplayPilot'
INPUT = ROOT/'research/burn10-state-replay-pilot-input.json'
REPORT = ROOT/'research/burn10-state-replay-pilot-checked.json'
FIELDS = ['machine', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history']
HEADER = '''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  Pipeline AdvancedPipeline StatePipeline StateOnlyCloseout StateBranchJoin CensusUnion.
Import ListNotations.
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, content):
    if path.exists():
        assert path.read_text() == content, f'Existing input changed: {path}'
    else:
        path.write_text(content)


def checker_source(rows):
    recipe = rows[0]
    mode = recipe['mode']
    if mode in ('finite', 'hist'):
        stage = (f'StateFinite {recipe["size"]} {recipe["anchor"]} {recipe["fuel"]} {recipe["extra"]}'
                 if mode == 'finite' else
                 f'StateHistory {recipe["history"]} {recipe["size"]} {recipe["anchor"]} {recipe["fuel"]} {recipe["extra"]}')
        data = ';'.join(f'{packed(r["machine"])}%N' for r in rows)
        body = f'''Definition rows : list N := [{data}].
Definition cert := {stage}.
Lemma checked : stp_batch_check 4096%N cert rows = true.
Proof. vm_compute. reflexivity. Qed.
Definition board := stp_board rows.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. exact (stp_batch_state_sound 4096%N cert rows checked). Qed.
'''
    else:
        data = ';\n'.join('(['+';'.join(map(str,codes(r['machine'])))+'], '+certificate(r)+')' for r in rows)
        body = f'''Definition rows : AdvancedBatch := [{data}].
Lemma checked : advanced_batch_check 4096%N 4096%N rows = true.
Proof. vm_compute. reflexivity. Qed.
Definition board := advanced_board rows.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof.
  intros family Hin tm Hle.
  exact (proj1 (advanced_board_sound 4096%N 4096%N rows checked family Hin tm Hle)).
Qed.
'''
    return HEADER + body + '''Lemma sound : StateBoardSound score board.
Proof.
  apply (state_board_N_weaken 4096%N scoreN board).
  - vm_compute. discriminate.
  - exact small_sound.
Qed.
Print Assumptions small_sound.
'''


def link_source(module):
    return HEADER + f'''From {NAMESPACE} Require Import {module}.
Definition board := {module}.board.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. exact {module}.small_sound. Qed.
Lemma sound : StateBoardSound score board.
Proof. exact {module}.sound. Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    if not INPUT.exists():
        selected = ROOT/'build/burn10-state-closeout/replay-pilot.json'
        diagnostic = ROOT/'research/burn10-state-closeout-summary.json'
        data = json.loads(selected.read_text())
        data['provenance'] = {str(p.relative_to(ROOT)): sha(p) for p in
                              (selected, diagnostic, ROOT/'research/burn10-state-closeout-input.json')}
        exact(INPUT, json.dumps(data, indent=2, sort_keys=True)+'\n')
    data = json.loads(INPUT.read_text())
    assert data['columns'] == FIELDS
    assert all(sha(ROOT/p) == h for p, h in data['provenance'].items())
    rows = [dict(zip(FIELDS, values)) for values in data['rows']]
    assert len(rows) == len({r['machine'] for r in rows}) == 24
    groups = defaultdict(list)
    for row in rows:
        assert row['bound'] == 4096
        groups[tuple(row[k] for k in FIELDS[1:])].append(row)
    assert len(groups) == 6 and all(len(g) == 4 for g in groups.values())
    files, links, inventory_machines, recipes = [], [], [], []
    for index, (recipe, selected) in enumerate(sorted(groups.items())):
        check = f'Checker{index:02}'
        link = f'Link{index:02}'
        path = BUILD/f'{check}.v'; exact(path, checker_source(selected)); files.append(path)
        path = BUILD/f'{link}.v'; exact(path, link_source(check)); files.append(path)
        links.append(link)
        inventory_machines.extend(r['machine'] for r in selected)
        recipes.append(dict(zip(FIELDS[1:], recipe), checker=check, link=link, rows=len(selected)))
    body = HEADER + f'From {NAMESPACE} Require Import '+ ' '.join(links)+'.\n'
    body += 'Definition boards : list (list TM) := ['+';'.join(m+'.board' for m in links)+'].\nDefinition board := concat boards.\n'
    for field, bound in (('small_sound', '(N.to_nat 4096%N)'), ('sound', 'score')):
        body += f'Lemma {field} : StateBoardSound {bound} board.\nProof. apply state_boards_sound. unfold boards.\n'
        body += forall_proof(links, field)+'\nQed.\n'
    body += 'Lemma was_pending : forall family, In family board -> bootstrap_pending family.\nProof. apply boards_pending. unfold boards.\n'
    body += forall_proof(links, 'was_pending')+'\nQed.\n'
    body += '''Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, QHBound score tm \/ pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ QHBound score tm /\ ~ pending tm.
Proof. exact (state_board_discharge _ _ was_pending sound). Qed.
Print Assumptions discharged.
'''
    path = BUILD/'Board.v'; exact(path, body); files.append(path)
    descriptor = dict(id='burn10_state_replay_pilot', scope='state', rows=24, state_bound=4096,
                      instruction_bound=None, module=NAMESPACE+'.Inventory', board='board', small_sound='small_sound',
                      sound='sound', was_pending='was_pending', proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)),
                      exact_inventory_theorem=NAMESPACE+'.Inventory.inventory_exact',
                      inventories=[dict(path='research/burn10-state-replay-pilot-machines.json',format='rows')],
                      load_paths=[dict(path=str(BUILD.relative_to(ROOT)),namespace=NAMESPACE)])
    path = BUILD/'Inventory.v'
    exact(path, inventory_source(dict(descriptor,module=NAMESPACE+'.Board',machines=inventory_machines))); files.append(path)
    paths = [(ROOT/'theories', 'BBB24'), (BUILD, NAMESPACE)]
    flags = [x for p, ns in paths for x in ('-Q',str(p),ns)]
    sources = dependency_hashes(files, flags)
    for name in ('check_burn10_state_replay_pilot.py','check_campaign.py','check_closure_wave.py',
                 'generate_pipeline_examples.py','check_shadow_links.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name] = sha(ROOT/'tools'/name)
    protected = {p: sha(p.with_suffix('.vo')) for p in (ROOT/k for k in sources)
                 if p.suffix == '.v' and not p.is_relative_to(BUILD)}
    input_hash = sha(INPUT)
    timings = {}
    for path in files:
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        timings[path.stem] = round(time.monotonic()-start, 3)
        print(path.stem, timings[path.stem], flush=True)
    receipt, log = kernel.fresh_paths(BUILD, 'kernel-audit')
    audit = kernel.audit([NAMESPACE+'.Inventory'], [files[-1]], paths, receipt, log,
                         recursive=True, timeout=args.audit_timeout)
    assert sha(INPUT) == input_hash and all(sha(ROOT/p) == h for p, h in sources.items())
    assert all(sha(p.with_suffix('.vo')) == h for p, h in protected.items())
    exact(ROOT/'research/burn10-state-replay-pilot-machines.json',
          json.dumps({'rows':[{'machine': m} for m in inventory_machines]}, indent=2)+'\n')
    report = dict(scope='24 exact state-bound families, all completions, linked to the frozen bootstrap. No global upper bound.',
                  checked_state_families=24, checked_instruction_families=0, descriptor=descriptor,
                  state_bound=4096, input_sha256=input_hash, source_sha256=sources,
                  compile_seconds=timings, stage_recipes=recipes,
                  audit_seconds=audit['elapsed_seconds'], checked_modules=len(audit['checked_modules']),
                  reused_modules=len(audit['reused_modules']), kernel_audit='Full recursive coqchk.',
                  kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
                  object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in files})
    exact(REPORT, json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'checked_state_families':24, 'compile_seconds':timings,
                      'audit_seconds':audit['elapsed_seconds']},indent=2),flush=True)


if __name__ == '__main__':
    main()
