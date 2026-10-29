"""Close the whole blank-initial class using eight checked source banks.

All generated Coq stays under build/. The stages are resumable, preserve old
objects, and audit their complete dependency closure before writing reports.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import time

from check_campaign import dependency_hashes, forall_proof
import kernel_audit_cache_v3 as kernel

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn15-blank-closeout'
NS='BBB24Burn15BlankCloseout'
INPUT=ROOT/'research/burn15-blank-closeout-input.json'
HEADER=f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census StateOnlyCloseout StateBranchJoin StatePipeline
  OneStateReach FamilyIndex Symmetry FamilyTransport.
From BBB24Burn14BlankFrontier Require Import BlankSources.
Import ListNotations.
'''


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def numbers(values):return '['+';'.join(f'{n}%N' for n in values)+']'


def write(name,source,files):
    path=BUILD/f'{name}.v';path.write_text(source);files.append(path)
    return path


def source_files(data):
    files=[]
    source=ROOT/'proof-sources/burn15-blank-closeout/Excerpts.v'
    write('Excerpts',source.read_text(),files)
    origins=[]
    for i,origin in enumerate(data['legacy_origins']):
        name=f'Narrow{i:03}';origins.append(name)
        entries=[e for e in data['_routed_origins'] if e['method']==origin['descriptor']['id']]
        assert entries and {n for e in entries for n in e['rows']}==set(origin['rows'])
        body=HEADER+f'From {NS} Require Import Excerpts.\n'
        body+='\n'.join('Require Import '+e['descriptor']['module']+'.' for e in entries)+'\n'
        submodules=[]
        for j,entry in enumerate(entries):
            sub=f'C{j:03}';submodules.append(sub)
            d=entry['descriptor'];module=d['module'];original=module+'.'+d['board'];bound=d['state_bound']
            check='excerpt_check' if entry['check']=='excerpt' else 'projection_check'
            sound='excerpt_state_sound' if entry['check']=='excerpt' else 'projection_state_sound'
            body+=f'Module {sub}.\nDefinition board := stp_board {numbers(entry["rows"])}.\n'
            body+=f'''Lemma checked : {check} {original} board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma original_sound : StateBoardSound (N.to_nat {bound}%N) {original}.
Proof.
'''
            if d['scope']=='both':
                body+=f'  intros family Hin complete Hle. exact (proj1 ({module}.{d["small_sound"]} family Hin complete Hle)).\n'
            elif d['scope']=='strong':
                body+=f'  intros family Hin complete Hle. exact (proj1 (strong_board_completions {bound}%N {d["instruction_bound"]}%N {original} {module}.{d["small_sound"]} family Hin complete Hle)).\n'
            else:body+=f'  exact {module}.{d["small_sound"]}.\n'
            body+=f'''Qed.
Lemma small_sound : StateBoardSound (N.to_nat {bound}%N) board.
Proof. exact ({sound} _ _ _ original_sound checked). Qed.
Lemma sound : StateBoardSound (N.to_nat 131072%N) board.
Proof.
  apply (state_board_N_weaken {bound}%N 131072%N board).
  - vm_compute. discriminate.
  - exact small_sound.
Qed.
'''
            body+=f'End {sub}.\n'
        body+='Definition boards := ['+';'.join(m+'.board' for m in submodules)+'].\nDefinition board := concat boards.\n'
        body+='Lemma sound : StateBoardSound (N.to_nat 131072%N) board.\nProof. apply state_boards_sound. unfold boards.\n'
        body+=forall_proof(submodules,'sound')+'\nQed.\n'
        write(name,body,files)
    body=HEADER+f'From {NS} Require Import '+' '.join(origins)+'.\n'
    body+='Definition boards := ['+';'.join(m+'.board' for m in origins)+'].\nDefinition board := concat boards.\n'
    body+='Lemma sound : StateBoardSound (N.to_nat 131072%N) board.\nProof. apply state_boards_sound. unfold boards.\n'
    body+=forall_proof(origins,'sound')+'\nQed.\n'
    write('LegacyAll',body,files)
    bank_parts=[]
    for i,bank in enumerate(data['source_banks']):
        body=f'Module B{i:03}.\n'
        for field in ('reach','legacy','routine'):
            body+=f'Definition {field} := stp_board {numbers(bank[field])}.\n'
        body+='''Lemma reach_checked : forallb ore_auto_state reach = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reach_sound : StateBoardSound (N.to_nat 131072%N) reach.
Proof. apply state_board_zero_weaken. exact (direct_reach_state_sound reach reach_checked). Qed.
Lemma legacy_checked : projection_check LegacyAll.board legacy = true.
Proof. vm_compute. reflexivity. Qed.
Lemma legacy_sound : StateBoardSound (N.to_nat 131072%N) legacy.
Proof. exact (projection_state_sound _ _ _ LegacyAll.sound legacy_checked). Qed.
Lemma routine_checked : projection_check BBB24Burn15BlankRoutine.Inventory.board routine = true.
Proof. vm_compute. reflexivity. Qed.
Lemma routine_sound : StateBoardSound (N.to_nat 131072%N) routine.
Proof.
  apply (state_board_N_weaken 4096%N 131072%N routine).
  - vm_compute. discriminate.
  - exact (projection_state_sound _ _ _ BBB24Burn15BlankRoutine.Inventory.small_sound routine_checked).
Qed.
Definition combined := concat [reach;legacy;routine].
Lemma combined_sound : StateBoardSound (N.to_nat 131072%N) combined.
Proof.
  apply state_boards_sound.
  apply Forall_cons; [exact reach_sound|].
  apply Forall_cons; [exact legacy_sound|].
  apply Forall_cons; [exact routine_sound|]. apply Forall_nil.
Qed.
'''
        body+=f'Definition board := stp_board {numbers(bank["sources"])}.\n'
        body+='''Lemma bank_checked : projection_check combined board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem sound : StateBoardSound (N.to_nat 131072%N) board.
Proof. exact (projection_state_sound _ _ _ combined_sound bank_checked). Qed.
'''
        body+=f'End B{i:03}.\n';bank_parts.append(body)
    body=HEADER+f'From {NS} Require Import LegacyAll.\nFrom BBB24Burn15BlankRoutine Require Import Inventory.\n'
    root=write('BankAll',body+'\n'.join(bank_parts),files)
    return files,[root]


def frontier_files(data):
    files=[]
    parts=[]
    for unit in data['units']:
        uid=unit['unit'];old=f'M{unit["module"]:03}.U{uid:03}';name=f'Frontier{uid:03}'
        body=f'Module {name}.\n'
        dependencies=[f'Frontier{d:03}' for d in unit['dependencies']]
        if unit['bank'] is None:
            assert not unit['rows']
            body+=f'''Lemma local_sound : StateBoardSound (N.to_nat 131073%N) {old}.local_frontier.
Proof. apply board_nil. Qed.
'''
        else:
            bankname=f'BankAll.B{unit["bank"]:03}'
            bank=data['source_banks'][unit['bank']]['sources'];raw=unit['rows']
            assert len(raw)%4==0
            body+='Definition rows : list BlankRow := [\n'
            body+=';\n'.join(f'blank_row {raw[i]}%N {bank[raw[i+1]]}%N {data["permutations"][raw[i+2]]} {str(bool(raw[i+3])).lower()}'
                               for i in range(0,len(raw),4))+'].\n'
            body+=f'''Definition board := blank_board rows.
Lemma checked : blank_batch_check {bankname}.board rows = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exact_checked : ordered_tables_same board {old}.local_frontier = true.
Proof. vm_compute. reflexivity. Qed.
Lemma frontier_exact : board = {old}.local_frontier.
Proof. exact (ordered_tables_same_sound _ _ exact_checked). Qed.
Theorem local_sound : StateBoardSound (N.to_nat 131073%N) {old}.local_frontier.
Proof.
  rewrite <- frontier_exact.
  exact (blank_batch_state_sound 131072%N {bankname}.board rows {bankname}.sound checked).
Qed.
'''
        body+=f'''Theorem sound : StateBoardSound (N.to_nat 131073%N) {old}.frontier.
Proof. apply board_app; [exact local_sound|]. apply state_boards_sound.
'''+forall_proof(dependencies,'sound')+'\nQed.\n'
        body+=f'End {name}.\n';parts.append(body)
    header=HEADER+'From BBB24Burn14BlankUnit Require Import OrderedTables.\n'
    header+='From BBB24Burn13StateCensus Require Import Join '+' '.join(f'M{i:03}' for i in range(len(data['modules'])))+'.\n'
    header+=f'From {NS} Require Import BankAll.\n'
    root=write('FrontiersAll',header+'\n'.join(parts),files)
    return files,[root]


def census_files(data):
    files=[];mapping={u['unit']:u['module'] for u in data['units']}
    for mid,group in enumerate(data['modules']):
        selected=group['units']
        imports=sorted({mapping[d] for uid in selected for d in data['units'][uid]['dependencies'] if mapping[d]!=mid})
        body=HEADER+'From BBB24Burn10StateCensus Require Import StateCensus.\n'
        body+=f'From BBB24Burn13StateCensus Require Import Join M{mid:03}.\n'
        if imports:body+=f'From {NS} Require Import '+' '.join(f'Census{i:03}' for i in imports)+'.\n'
        for uid in selected:
            unit=data['units'][uid];deps=unit['dependencies'];old=f'M{mid:03}.U{uid:03}'
            names={d:(f'U{d:03}' if mapping[d]==mid else f'Census{mapping[d]:03}.U{d:03}') for d in deps}
            body+=f'''Module U{uid:03}.
Definition family := {old}.family.
Definition frontier := {old}.frontier.
Definition lookup_board := {old}.lookup_board.
Definition leaf_check := {old}.leaf_check.
Definition certificate := {old}.certificate.
Lemma checked : state_verify 131073%N StateLookup leaf_check {unit['depth']} family certificate = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lookup_sound : StateBoardSound (N.to_nat 131073%N) frontier ->
  StateBoardSound (N.to_nat 131073%N) lookup_board.
Proof.
  intro H. destruct (frontier_parts (N.to_nat 131073%N) {old}.local_frontier {old}.dependency_frontiers H) as [HL HD].
'''
            for i,d in enumerate(deps):
                tail='HD' if i==0 else f'HT{i-1}'
                body+=f'  inversion {tail} as [| ? ? H{i} HT{i}]; subst; clear {tail}.\n'
            body+=f'  apply board_app; [exact HL|]. unfold {old}.dependency_roots.\n'
            for i,d in enumerate(deps):body+=f'  apply board_cons; [exact ({names[d]}.sound H{i})|].\n'
            body+='  apply board_nil.\nQed.\n'
            body+=f'''Theorem sound : StateBoardSound (N.to_nat 131073%N) frontier ->
  forall complete, TM_le family complete -> QHBound (N.to_nat 131073%N) complete.
Proof.
  intro H. exact (state_verify_sound 131073%N StateLookup leaf_check
    (fun f w => state_lookup_sound (N.to_nat 131073%N) lookup_board f w (lookup_sound H))
    {unit['depth']} family certificate checked).
Qed.
End U{uid:03}.
'''
        write(f'Census{mid:03}',body,files)
    root=data['root_unit'];mid=mapping[root]
    body=HEADER+f'From {NS} Require Import Census{mid:03} FrontiersAll.\n'
    body+=f'''Definition family := Census{mid:03}.U{root:03}.family.
Theorem blank_family_sound : forall complete, TM_le family complete ->
  QHBound (N.to_nat 131073%N) complete.
Proof. exact (Census{mid:03}.U{root:03}.sound FrontiersAll.Frontier{root:03}.sound). Qed.
Theorem blank_family_score : forall complete, TM_le family complete -> QHBound score complete.
Proof.
  intros complete Hle.
  assert (H : StateBoardSound (N.to_nat 131073%N) [family]).
  {{ intros target [<-|Hfalse] tm Htm; [exact (blank_family_sound tm Htm)|contradiction]. }}
  pose proof (state_board_N_weaken 131073%N scoreN [family]) as W.
  assert (Hbudget : (131073 <= scoreN)%N). {{ vm_compute. discriminate. }}
  exact (W Hbudget H family (or_introl eq_refl) complete Hle).
Qed.
Print Assumptions blank_family_sound.
Print Assumptions blank_family_score.
'''
    write('BlankBound',body,files)
    return files,[files[-1]]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage',choices=['sources','frontiers','census'],required=True)
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--memory-mib',type=int,default=8192)
    parser.add_argument('--resume',action='store_true')
    args=parser.parse_args();BUILD.mkdir(parents=True,exist_ok=True)
    assert args.memory_mib > 0 and args.timeout > 0
    memory_bytes=args.memory_mib*1024*1024
    resource.setrlimit(resource.RLIMIT_AS,(memory_bytes,memory_bytes))
    # Match the campaign runner: bound unused OCaml heap slack while importing
    # the legacy certificate environment, without changing proof checking.
    os.environ.setdefault('OCAMLRUNPARAM','o=5,O=10')
    data=json.loads(INPUT.read_text());input_hash=sha(INPUT)
    routing_path=ROOT/'research/burn15-legacy-routing-input.json'
    routing=json.loads(routing_path.read_text());routing_hash=sha(routing_path)
    assert routing['original_input_sha256']==input_hash
    assert all(sha(ROOT/path)==digest for path,digest in routing['source_sha256'].items())
    data['_routed_origins']=routing['origins']
    assert data['state_bound']==131073 and data['source_bound']==131072
    assert data['raw_frontier_rows']==63426 and data['canonical_sources']==10572
    assert all(sha(ROOT/path)==digest for path,digest in data['provenance'].items())
    routine_report=ROOT/'research/burn15-blank-routine-checked.json'
    routine=json.loads(routine_report.read_text())
    assert routine['checked_state_source_families']==3692 and routine['state_bound']==4096
    paths={'theories':'BBB24','build/burn10-state-closeout/prototype':'BBB24Burn10StateCensus',
        'build/burn13-state-census':'BBB24Burn13StateCensus',
        'build/burn14-blank-frontier/pilot':'BBB24Burn14BlankFrontier',
        'build/burn14-blank-frontier/unit-pilot':'BBB24Burn14BlankUnit',
        'build/burn15-blank-routine':'BBB24Burn15BlankRoutine',str(BUILD.relative_to(ROOT)):NS}
    for origin in data['legacy_origins']:
        for item in origin['descriptor']['load_paths']:
            previous=paths.setdefault(item['path'],item['namespace']);assert previous==item['namespace']
    loadpaths=[(ROOT/path,namespace) for path,namespace in paths.items()]
    flags=[x for path,namespace in loadpaths for x in ('-Q',str(path),namespace)]
    files,roots={'sources':source_files,'frontiers':frontier_files,'census':census_files}[args.stage](data)
    sources=dependency_hashes(files,flags)
    for path in [Path(__file__),ROOT/'tools/check_campaign.py',ROOT/'tools/kernel_audit_cache_v3.py',
                 ROOT/'proof-sources/burn15-blank-closeout/Excerpts.v']:
        sources[str(path.relative_to(ROOT))]=sha(path)
    protected={p.with_suffix('.vo'):sha(p.with_suffix('.vo')) for p in (ROOT/path for path in sources)
               if p.suffix=='.v' and p not in files and 'proof-sources' not in p.parts}
    runtime={name:sha(Path(shutil.which(name))) for name in ('coqc','coqdep','coqchk')}
    # Source hashes for the entire selected closure are already pinned above.
    # Hash each existing object once, then refresh an entry after compilation.
    # The final kernel audit and protected-object check remain mandatory.
    object_hashes={path:sha((ROOT/path).with_suffix('.vo')) for path in sources
                   if path.endswith('.v') and 'proof-sources/' not in path
                   and (ROOT/path).with_suffix('.vo').exists()}
    timings={}
    for i,path in enumerate(files):
        dump(BUILD/'status.json',dict(stage=args.stage,pid=os.getpid(),module=path.stem,index=i,total=len(files),updated_unix=time.time()))
        record=path.with_suffix('.compiled.json');obj=path.with_suffix('.vo')
        if args.resume and record.exists() and obj.exists():
            prior=json.loads(record.read_text())
            if (prior.get('runtime')==runtime
                and all(sources.get(k)==v for k,v in prior['sources'].items())
                and all(object_hashes.get(k)==v for k,v in prior['dependency_objects'].items())
                and prior.get('object_sha256')==object_hashes.get(str(path.relative_to(ROOT)))):
                timings[path.stem]=0.0;print('Resumed',path.stem,flush=True);continue
        deps=dependency_hashes([path],flags)
        evidence=dict(runtime=runtime,sources=deps,
            dependency_objects={p:object_hashes[p] for p in deps if ROOT/p!=path})
        start=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-time','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        elapsed=round(time.monotonic()-start,3);timings[path.stem]=elapsed
        object_hashes[str(path.relative_to(ROOT))]=sha(obj)
        dump(record,dict(evidence,object_sha256=sha(obj),elapsed_seconds=elapsed))
        print(path.stem,elapsed,flush=True)
    cache=[ROOT/'build/campaign-final/campaign-audit-000003.json',ROOT/routine['kernel_receipt'],
        ROOT/'build/burn3-history/proof/kernel-audit.json',
        ROOT/'build/burn13-state-census/ConditionalBlank-audit.json',
        ROOT/'build/burn14-blank-frontier/pilot/kernel-audit.json',
        ROOT/'build/burn14-blank-frontier/unit-pilot/kernel-audit.json']
    for stage in ('sources','frontiers'):
        if stage==args.stage:break
        report=ROOT/f'research/burn15-blank-closeout-{stage}-checked.json'
        cache.append(ROOT/json.loads(report.read_text())['kernel_receipt'])
    receipt,log=kernel.fresh_paths(BUILD,args.stage+'-audit')
    dump(BUILD/'status.json',dict(stage=args.stage,phase='auditing',pid=os.getpid(),updated_unix=time.time()))
    audit=kernel.audit([NS+'.'+p.stem for p in roots],roots,loadpaths,receipt,log,cache=cache,recursive=False,timeout=3600)
    assert sha(INPUT)==input_hash
    assert sha(routing_path)==routing_hash
    assert all(sha(ROOT/path)==digest for path,digest in sources.items())
    assert all(sha(path)==digest for path,digest in protected.items())
    assert all(sha(ROOT/path)==digest for path,digest in data['provenance'].items())
    stable=dict(stage=args.stage,input_sha256=input_hash,source_sha256=sources,
        legacy_routing_input_sha256=routing_hash,
        focused_routine_report_sha256=sha(routine_report),source_bound=131072,frontier_bound=131073,
        scope={'sources':'Eight source banks, all completions; no additive distinct-family credit.',
               'frontiers':'All63426 exact raw blank-census frontier leaves, all completions.',
               'census':'Unconditional initial instruction0LB class, all completions; state bound131073.'}[args.stage],
        unconditional_blank_class_proved=args.stage=='census',global_upper_bound_proved=False,
        source_counts=data['source_counts'],raw_frontier_rows=63426,
        theorem=NS+'.BlankBound.blank_family_sound' if args.stage=='census' else None,
        kernel_audit='Complete transitive dependency closure via validated V3 exact-artifact receipts and all uncached modules.')
    result=dict(stable,compile_seconds=timings,audit_seconds=audit['elapsed_seconds'],
        checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
        kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt))
    report=ROOT/f'research/burn15-blank-closeout-{args.stage}-checked.json'
    if report.exists():
        prior=json.loads(report.read_text());assert all(prior[k]==v for k,v in stable.items())
    else:dump(report,result)
    dump(BUILD/f'{args.stage}-current-proof-receipt.json',result)
    dump(BUILD/'status.json',dict(stage=args.stage,phase='audited',pid=os.getpid(),report=str(report.relative_to(ROOT)),updated_unix=time.time()))
    print('AUDITED',args.stage,audit['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
