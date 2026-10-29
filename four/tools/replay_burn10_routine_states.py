"""Resumable state replay of the original cheap-search queue.

Compact inputs use packed tables grouped by shared recipe. Ordinary replay
needs no ignored search files. Finite/history/RepWL use existing state-only
checkers; plain n-grams project the existing both-bound checker. Generated
proof shards stay ignored, and no checked report precedes a kernel audit.
"""
import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

from check_campaign import inventory_source, packed, unpack, forall_proof
from check_shadow_links import dependency_hashes
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/burn10-routine-states'
NAMESPACE = 'BBB24Burn10RoutineStates'
FIELDS = ('mode','bound','size','anchor','fuel','extra','history')
HEADER = '''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout Pipeline
  AdvancedPipeline StatePipeline StateRepWLBatch StateOnlyCloseout StateBranchJoin CensusUnion.
Import ListNotations.
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, content):
    if path.exists():
        assert path.read_text() == content, f'Frozen input/source changed: {path}'
    else:
        path.write_text(content)


def dump(path, data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def prepare(path, benchmark):
    candidates=ROOT/'build/burn10-state-closeout/unreplayed-cheap-candidates.tsv'
    diagnostic_path=ROOT/'research/burn10-state-closeout-summary.json'
    diagnostic=json.loads(diagnostic_path.read_text())
    assert sha(candidates)==diagnostic['unmatched_cheap_candidates_sha256']
    excluded=set(); provenance={'diagnostic_sha256':sha(diagnostic_path),'candidates_sha256':sha(candidates)}
    for batch in ('pilot','64'):
        prior=ROOT/f'research/burn10-state-replay-{batch}-input.json'
        report=ROOT/f'research/burn10-state-replay-{batch}-checked.json'
        data=json.loads(prior.read_text()); checked=json.loads(report.read_text())
        assert sha(prior)==checked['input_sha256']
        excluded.update(row[0] for row in data['rows'])
        provenance[prior.name]=sha(prior);provenance[report.name]=sha(report)
    assert len(excluded)==408
    groups=defaultdict(list)
    with candidates.open() as stream:
        for raw in csv.DictReader(stream,delimiter='\t'):
            if raw['machine'] not in excluded:
                recipe=tuple(raw[k] if k=='mode' else int(raw[k]) for k in FIELDS)
                groups[recipe].append(raw['machine'])
    assert len(groups)==6 and sum(map(len,groups.values()))==124114
    selected=[]
    for recipe,machines in sorted(groups.items()):
        machines.sort(key=lambda m:hashlib.sha256(m.encode()).digest())
        if benchmark:machines=machines[:256]
        selected.append(dict(certificate=dict(zip(FIELDS,recipe)),rows=[packed(m) for m in machines]))
    metadata=dict(scope='State only, all completions. No instruction/global upper-bound claim.',
                  encoding='Eight base17 cells, A0 least significant;16 means undefined.',
                  selection='Per-recipe machine SHA256 order after excluding the frozen408 audited routine rows',
                  selected_rows=sum(len(g['rows']) for g in selected),shard_size=256,
                  mode='benchmark256' if benchmark else 'full',provenance=provenance)
    prefix=json.dumps(metadata,indent=2,sort_keys=True)[:-2]
    bodies=[]
    for group in selected:
        head=json.dumps({'certificate':group['certificate']},indent=2,sort_keys=True)[:-2]
        chunks=[', '.join(map(str,group['rows'][i:i+24])) for i in range(0,len(group['rows']),24)]
        bodies.append(head+',\n  "rows": [\n    '+',\n    '.join(chunks)+'\n  ]\n}')
    exact(path,prefix+',\n  "groups": [\n'+',\n'.join(bodies)+'\n  ]\n}\n')


def checker_source(numbers, recipe):
    body=';\n  '.join(';'.join(f'{v}%N' for v in numbers[i:i+16]) for i in range(0,len(numbers),16))
    source=HEADER+f'Definition rows : list N := [\n  {body}].\nDefinition board := stp_board rows.\n'
    mode,n,t,fuel,extra,history=(recipe[k] for k in ('mode','size','anchor','fuel','extra','history'))
    if mode=='rw':
        source+=f'''Definition cert := mkSRWStage {n} {extra} {t} {fuel}.
Lemma checked : srw_batch_check 4096%N cert rows = true.
Proof. vm_compute. reflexivity. Qed.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. exact (srw_batch_state_sound 4096%N cert rows checked). Qed.
'''
    elif mode in ('finite','hist'):
        cert=f'StateFinite {n} {t} {fuel} {extra}' if mode=='finite' else f'StateHistory {history} {n} {t} {fuel} {extra}'
        source+=f'''Definition cert := {cert}.
Lemma checked : stp_batch_check 4096%N cert rows = true.
Proof. vm_compute. reflexivity. Qed.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. exact (stp_batch_state_sound 4096%N cert rows checked). Qed.
'''
    else:
        assert mode=='ng'
        source+=f'''Definition cert := ExistingStage (NGram {n} {t} {fuel} {extra}).
Lemma checked : forallb (fun packed => advanced_check 4096%N 4096%N (stp_machine packed) cert) rows = true.
Proof. vm_compute. reflexivity. Qed.
Lemma small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof.
  intros family Hin complete Hle. apply in_map_iff in Hin as (packed & <- & Hin).
  pose proof checked as H. apply forallb_forall with (x:=packed) in H; [|exact Hin].
  exact (proj1 (advanced_completions 4096%N 4096%N (stp_machine packed) cert H complete Hle)).
Qed.
'''
    return source+'''Lemma sound : StateBoardSound score board.
Proof.
  apply (state_board_N_weaken 4096%N scoreN board).
  - vm_compute. discriminate.
  - exact small_sound.
Qed.
'''


def link_source(module):
    return HEADER+f'''From {NAMESPACE} Require Import {module}.
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


def aggregate_source(modules):
    body=HEADER+f'From {NAMESPACE} Require Import '+ ' '.join(modules)+'.\n'
    body+='Definition boards : list (list TM) := ['+';'.join(m+'.board' for m in modules)+'].\nDefinition board := concat boards.\n'
    for field,bound in (('small_sound','(N.to_nat 4096%N)'),('sound','score')):
        body+=f'Lemma {field} : StateBoardSound {bound} board.\nProof. apply state_boards_sound. unfold boards.\n'
        body+=forall_proof(modules,field)+'\nQed.\n'
    body+='Lemma was_pending : forall family, In family board -> bootstrap_pending family.\nProof. apply boards_pending. unfold boards.\n'
    body+=forall_proof(modules,'was_pending')+'\nQed.\n'
    return body+r'''Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, QHBound score tm \/ pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ QHBound score tm /\ ~ pending tm.
Proof. exact (state_board_discharge _ _ was_pending sound). Qed.
Print Assumptions discharged.
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch',choices=('benchmark256','full'),default='benchmark256')
    parser.add_argument('--prepare',action='store_true')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--workers',type=int,default=1)
    parser.add_argument('--timeout',type=int,default=120)
    parser.add_argument('--audit-timeout',type=int,default=36000)
    parser.add_argument('--audit-cache',type=Path,action='append',default=[])
    args=parser.parse_args();assert 1<=args.workers<=2
    benchmark=args.batch=='benchmark256'
    input_path=ROOT/f'research/burn10-routine-states-{args.batch}-input.json'
    report_path=ROOT/f'research/burn10-routine-states-{args.batch}-checked.json'
    BUILD.mkdir(parents=True,exist_ok=True)
    if args.prepare and not input_path.exists():prepare(input_path,benchmark)
    data=json.loads(input_path.read_text());groups=data['groups']
    assert data['shard_size']==256 and len(groups)==6 and data['mode']==args.batch
    all_numbers=[n for group in groups for n in group['rows']]
    assert len(all_numbers)==len(set(all_numbers))==data['selected_rows']==(1536 if benchmark else 124114)
    for group in groups:
        recipe=group['certificate'];assert set(recipe)==set(FIELDS) and recipe['bound']==4096
        assert recipe['mode'] in ('ng','rw','finite','hist')
        machines=[unpack(n,17) for n in group['rows']]
        assert machines==sorted(machines,key=lambda m:hashlib.sha256(m.encode()).digest())
    loadpaths=[(ROOT/'theories','BBB24'),(BUILD,NAMESPACE)]
    flags=[x for p,ns in loadpaths for x in ('-Q',str(p),ns)]
    files, jobs, links, timings=[],[],[],{}
    for stage,group in enumerate(groups):
        for offset in range(0,len(group['rows']),256):
            suffix=f'S{stage:02}_{offset//256:04}'
            checker,link='Checker'+suffix,'Link'+suffix
            cp,lp=BUILD/f'{checker}.v',BUILD/f'{link}.v'
            exact(cp,checker_source(group['rows'][offset:offset+256],group['certificate']))
            exact(lp,link_source(checker));files.extend([cp,lp]);jobs.append((cp,lp));links.append(link)
    label='Benchmark' if benchmark else 'Full'
    aggregate=BUILD/f'{label}Board.v';exact(aggregate,aggregate_source(links));files.append(aggregate)
    descriptor=dict(id='burn10_routine_states_'+args.batch,scope='state',rows=len(all_numbers),state_bound=4096,
                    instruction_bound=None,module=NAMESPACE+'.'+label+'Inventory',board='board',small_sound='small_sound',
                    sound='sound',was_pending='was_pending',proof_source=str((BUILD/f'{label}Inventory.v').relative_to(ROOT)),
                    exact_inventory_theorem=NAMESPACE+'.'+label+'Inventory.inventory_exact',
                    inventories=[dict(path=str(input_path.relative_to(ROOT)),format='packed17_groups')],
                    load_paths=[dict(path=str(BUILD.relative_to(ROOT)),namespace=NAMESPACE)])
    inventory=BUILD/f'{label}Inventory.v'
    exact(inventory,inventory_source(dict(descriptor,module=NAMESPACE+'.'+label+'Board',machines=[unpack(n,17) for n in all_numbers])))
    files.append(inventory)
    core=dependency_hashes([ROOT/'theories'/f'{name}.v' for name in
          ('AdvancedPipeline','StatePipeline','StateRepWLBatch','Bootstrap','StateBranchJoin','CensusUnion')],flags)
    objects={name:sha((ROOT/name).with_suffix('.vo')) for name in core}
    helpers={f'tools/{name}':sha(ROOT/'tools'/name) for name in
             ('replay_burn10_routine_states.py','check_campaign.py','check_shadow_links.py','kernel_audit_cache_v3.py')}
    runtime={name:sha(Path(shutil.which(name))) for name in ('coqc','coqdep','coqchk')}
    baseline=dict(sources=core,objects=objects,helpers=helpers,runtime=runtime)
    baseline_hash=hashlib.sha256(json.dumps(baseline,sort_keys=True).encode()).hexdigest()
    stable=dict(scope='Exact routine state families from the earlier cheap-search queue; all completions; no global bound.',
                checked_state_families=len(all_numbers),checked_instruction_families=0,state_bound=4096,descriptor=descriptor,
                input_sha256=sha(input_path),source_sha256={**dependency_hashes(files,flags),**helpers},
                stage_counts=[dict(certificate=g['certificate'],rows=len(g['rows'])) for g in groups],
                base_dependency_sha256=baseline_hash)
    if report_path.exists():
        old=json.loads(report_path.read_text());assert all(old[k]==v for k,v in stable.items())

    def compile_file(path, extra=()):
        evidence=dict(source_sha256=sha(path),base_dependency_sha256=baseline_hash,
                      prerequisites={p.name:dict(source=sha(p),object=sha(p.with_suffix('.vo'))) for p in extra})
        receipt=path.with_suffix('.compiled.json');obj=path.with_suffix('.vo')
        if args.resume and receipt.exists() and obj.exists():
            old=json.loads(receipt.read_text())
            if all(old.get(k)==v for k,v in evidence.items()) and old.get('object_sha256')==sha(obj):
                return 0.0
        start=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        elapsed=round(time.monotonic()-start,3)
        dump(receipt,dict(evidence,object_sha256=sha(obj),elapsed_seconds=elapsed))
        return elapsed

    def compile_job(job):
        cp,lp=job
        result={cp.stem:compile_file(cp)}
        result[lp.stem]=compile_file(lp,[cp])
        return result

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for future in as_completed([pool.submit(compile_job,job) for job in jobs]):
            result=future.result();timings.update(result);print(json.dumps(result),flush=True)
    timings[aggregate.stem]=compile_file(aggregate,[job[1] for job in jobs])
    timings[inventory.stem]=compile_file(inventory,[aggregate])
    receipt,log=kernel.fresh_paths(BUILD,args.batch+'-kernel-audit')
    audit=kernel.audit([descriptor['module']],[inventory],loadpaths,receipt,log,cache=args.audit_cache,
                       recursive=not args.audit_cache,timeout=args.audit_timeout)
    assert sha(input_path)==stable['input_sha256']
    assert all(sha(ROOT/p)==h for p,h in stable['source_sha256'].items())
    assert all(sha((ROOT/p).with_suffix('.vo'))==h for p,h in objects.items())
    result=dict(stable,compile_seconds=timings,audit_seconds=audit['elapsed_seconds'],
                checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
                kernel_audit='Full recursive coqchk.' if audit['kind']=='recursive' else 'Complete dependency closure via validated exact-artifact audit receipts.',
                kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt))
    if not report_path.exists():dump(report_path,result)
    dump(BUILD/f'{args.batch}-current-proof-receipt.json',result)
    print(json.dumps(dict(checked_state_families=len(all_numbers),audit_seconds=audit['elapsed_seconds'],
                         compile_seconds=timings),indent=2),flush=True)


if __name__=='__main__':main()
