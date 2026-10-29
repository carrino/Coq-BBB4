"""Focused state replay of all 3692 routine sources needed by the blank census.

This overlaps the large routine replay and its earlier benchmarks; its counts
must never be added as distinct-family credit. Generated proof files stay ignored.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from check_campaign import inventory_source, packed, unpack, forall_proof
from check_shadow_links import dependency_hashes
from replay_burn10_routine_states import checker_source, FIELDS
import kernel_audit_cache_v3 as kernel

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn15-blank-routine'
NS='BBB24Burn15BlankRoutine'
INPUT=ROOT/'research/burn15-blank-routine-input.json'
REPORT=ROOT/'research/burn15-blank-routine-checked.json'
HEADER='''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout CensusUnion
  StateOnlyCloseout StateBranchJoin StatePipeline.
Import ListNotations.
'''


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare():
    catalog=json.loads((ROOT/'build/burn14-blank-frontier/sources.json').read_text())['rows']
    selected={s['packed'] for s in catalog if s['kind'].startswith('routine')}
    assert len(selected)==3692
    full_path=ROOT/'research/burn10-routine-states-full-input.json'
    prior_path=ROOT/'research/burn10-state-replay-64-input.json'
    full=json.loads(full_path.read_text());prior=json.loads(prior_path.read_text())
    recipes={n:g['certificate'] for g in full['groups'] for n in g['rows'] if n in selected}
    for values in prior['rows']:
        row=dict(zip(prior['columns'],values));number=packed(row['machine'])
        if number in selected:
            assert number not in recipes
            recipes[number]={k:row[k] for k in FIELDS}
    assert set(recipes)==selected
    groups=[]
    for recipe in [g['certificate'] for g in full['groups']]:
        numbers=sorted(n for n,r in recipes.items() if r==recipe)
        assert numbers
        groups.append(dict(certificate=recipe,rows=numbers))
    assert sum(len(g['rows']) for g in groups)==3692
    data=dict(scope='State-only blank shadow sources. Overlaps the full routine replay; no additive distinct-family credit.',
        encoding='Eight base17 cells, A0 least significant;16 is undefined.',selected_rows=3692,shard_size=256,
        provenance={str(p.relative_to(ROOT)):sha(p) for p in [full_path,prior_path,
            ROOT/'research/burn14-blank-frontier-plan.json']},groups=groups)
    text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if INPUT.exists():assert INPUT.read_text()==text
    else:INPUT.write_text(text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare',action='store_true')
    args=parser.parse_args()
    BUILD.mkdir(parents=True,exist_ok=True)
    if args.prepare:prepare()
    data=json.loads(INPUT.read_text());numbers=[n for g in data['groups'] for n in g['rows']]
    assert data['selected_rows']==len(numbers)==len(set(numbers))==3692 and data['shard_size']==256
    assert len(data['groups'])==6
    paths=[(ROOT/'theories','BBB24'),(BUILD,NS)]
    flags=[x for path,namespace in paths for x in ('-Q',str(path),namespace)]
    files=[];modules=[]
    def emit(name,text):
        path=BUILD/f'{name}.v';path.write_text(text);files.append(path)
    for stage,group in enumerate(data['groups']):
        assert group['certificate']['bound']==4096
        for offset in range(0,len(group['rows']),256):
            name=f'CheckerS{stage:02}_{offset//256:03}';modules.append(name)
            body=checker_source(group['rows'][offset:offset+256],group['certificate'])
            body+='''Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
'''
            emit(name,body)
    body=HEADER+f'From {NS} Require Import '+' '.join(modules)+'.\n'
    body+='Definition boards := ['+';'.join(m+'.board' for m in modules)+'].\nDefinition board := concat boards.\n'
    for field,bound in [('small_sound','(N.to_nat 4096%N)'),('sound','score')]:
        body+=f'Lemma {field} : StateBoardSound {bound} board.\nProof. apply state_boards_sound. unfold boards.\n'
        body+=forall_proof(modules,field)+'\nQed.\n'
    body+='Lemma was_pending : forall family, In family board -> bootstrap_pending family.\nProof. apply boards_pending. unfold boards.\n'
    body+=forall_proof(modules,'was_pending')+'\nQed.\n'
    emit('Board',body)
    descriptor=dict(id='burn15_blank_routine_sources',module=NS+'.Inventory',board='board',small_sound='small_sound',
        sound='sound',was_pending='was_pending',scope='state',state_bound=4096,instruction_bound=None,rows=3692,
        inventories=[dict(path=str(INPUT.relative_to(ROOT)),format='packed17_groups')],
        load_paths=[dict(path=str(BUILD.relative_to(ROOT)),namespace=NS)],
        exact_inventory_theorem=NS+'.Inventory.inventory_exact',proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)))
    emit('Inventory',inventory_source(dict(descriptor,module=NS+'.Board',machines=[unpack(n,17) for n in numbers])))
    hashes=dependency_hashes(files,flags)
    for name in ['replay_burn15_blank_routine_sources.py','replay_burn10_routine_states.py',
                 'check_campaign.py','check_shadow_links.py','kernel_audit_cache_v3.py']:
        hashes['tools/'+name]=sha(ROOT/'tools'/name)
    protected={p.with_suffix('.vo'):sha(p.with_suffix('.vo')) for p in (ROOT/k for k in hashes)
               if p.suffix=='.v' and p not in files}
    input_hash=sha(INPUT);timings={}
    for path in files:
        start=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120)
        timings[path.stem]=round(time.monotonic()-start,3);print(path.stem,timings[path.stem],flush=True)
    receipt,log=kernel.fresh_paths(BUILD,'kernel-audit')
    audit=kernel.audit([NS+'.Inventory'],[files[-1]],paths,receipt,log,recursive=True,timeout=1800)
    assert sha(INPUT)==input_hash
    assert all(sha(ROOT/path)==digest for path,digest in hashes.items())
    assert all(sha(path)==digest for path,digest in protected.items())
    stable=dict(scope=data['scope'],checked_state_source_families=3692,additive_family_credit=0,state_bound=4096,
        input_sha256=input_hash,source_sha256=hashes,descriptor=descriptor,
        stage_counts=[dict(certificate=g['certificate'],rows=len(g['rows'])) for g in data['groups']],
        full_blank_root_proved=False,global_upper_bound_proved=False,kernel_audit='Full recursive coqchk.')
    result=dict(stable,compile_seconds=timings,audit_seconds=audit['elapsed_seconds'],
        checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
        kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt))
    if REPORT.exists():
        old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items())
    else:REPORT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    (BUILD/'current-proof-receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('AUDITED3692',audit['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
