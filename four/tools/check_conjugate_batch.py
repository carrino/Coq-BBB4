"""Replay compact two-prefix conjugacy witnesses against proved source boards.

Default replay needs tracked inputs plus the reproduced Coq source boards.
Only --select reads the large ignored survey and runs the untrusted C++ search.
Search hashes are never evidence: exact Python simulation precedes Coq replay.
Use --refresh to publish a report after a recursive kernel audit. Local optional
--cache receipts allow incremental development; their reports are explicitly
labelled and require a final recursive combined audit before a census update.
"""
import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
from pathlib import Path

import group_families as grouping
from generate_pipeline_examples import codes
from kernel_audit_cache import audit, digest, fresh_paths

ROOT=Path(__file__).resolve().parents[1]
DEFAULT_CONFIG=ROOT/'research/conjugate-sources-r000.json'
DEFAULT_INPUT=ROOT/'research/conjugate-input-r000.json'
SHARD_SIZE=128


def inventory_hash(machines):
    return hashlib.sha256(('\n'.join(machines)+'\n').encode()).hexdigest()


def identifier(value):
    if not isinstance(value,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',value):
        raise ValueError(f'Invalid Coq identifier: {value!r}')
    return value


def machine_rows(entry):
    data=json.loads((ROOT/entry['path']).read_text())
    kind=entry['format']
    if kind=='transport_images':return [r[0] for key in ('images','shadow_images') for r in data[key]]
    if kind=='json_rows':return [r['machine'] for r in data['rows']]
    if kind=='json_columns':return [r[data['columns'].index('machine')] for r in data['rows']]
    if kind=='root_cycle_rows':return [r[0] for r in data['rows'] if r[1][0]=='C']
    raise ValueError(f'Unknown machine inventory format {kind}')


def sources(path):
    config=json.loads(path.read_text());machines=[];inputs={str(path.relative_to(ROOT)):digest(path)}
    loadpaths=[(ROOT/'theories','BBB24')]
    for source in config['sources']:
        for key in ('module','board','nonhalt','small_sound','sound'):
            identifier(source[key])
        if source.get('was_pending'):identifier(source['was_pending'])
        if type(source['bound']) is not int or not 0<=source['bound']<=config['source_bound']:
            raise ValueError('Invalid source bound')
        new=[]
        for entry in source['machine_inputs']:
            inputs[entry['path']]=digest(ROOT/entry['path']);new+=machine_rows(entry)
        for m in new:codes(m)
        source['count']=len(new);machines+=new
        for key in ('proof_source','audited_report'):
            inputs[source[key]]=digest(ROOT/source[key])
        if not (ROOT/source['proof_source']).with_suffix('.vo').is_file():
            raise ValueError('Reproduce source board first: '+source['proof_source'])
        for entry in source['load_paths']:
            identifier(entry['namespace']);pair=(ROOT/entry['path'],entry['namespace'])
            if pair not in loadpaths:loadpaths.append(pair)
    return config,machines,inputs,loadpaths


def key(machine):
    result=1
    for c in codes(machine):result=17*result+c
    return result


def exact_config(machine,state,steps):
    tape={};head=0;table=codes(machine)
    for _ in range(steps):
        tr=table[4*state+tape.get(head,0)]
        if tr==16:raise ValueError('Witness boot halts')
        write=tr//4
        if write:tape[head]=write
        else:tape.pop(head,None)
        head+=1 if (tr//2)%2 else -1;state=tr%2
    return state,tuple(sorted((p-head,s) for p,s in tape.items()))


def validate(data,machines,config):
    if data['source_inventory_sha256']!=inventory_hash(machines):
        raise ValueError('Ordered source inventory changed; explicitly regenerate selection')
    if data['source_bound']!=config['source_bound'] or data['output_bound']!=config['output_bound']:
        raise ValueError('Selected witness bounds changed')
    known=set(machines);seen=set()
    for row in data['rows']:
        if len(row)!=7:raise ValueError('Malformed conjugacy row')
        target,source,p,mirror,destination,origin,survivor=row
        codes(target);codes(source)
        if target in seen or source not in known:raise ValueError('Duplicate target or unknown proved source')
        seen.add(target)
        if p not in {'P'+''.join(map(str,p[1:])) for p in grouping.PERMS}:raise ValueError('Invalid permutation')
        if type(mirror) is not bool or type(survivor) is not bool:raise ValueError('Invalid Boolean witness')
        if any(type(n) is not int or not 0<=n<=1000000 for n in (destination,origin)):
            raise ValueError('Boot bound out of range')
        if config['source_bound']+destination>config['output_bound']:raise ValueError('Output bound is too small')
        transformed=grouping.rename(grouping.parse(target),(0,)+tuple(map(int,p[1:])),mirror=mirror,swap=True)
        if any(a!='---' and a!=b for a,b in zip(grouping.parse(source),transformed)):
            raise ValueError('Source table is not included in transformed target')
        if exact_config(target,0,destination)!=exact_config(target,1,origin):
            raise ValueError('Exact boot configurations differ')


def patterns(machines,swap):
    result={}
    for source in machines:
        for p in grouping.PERMS:
            for mirror in (False,True):
                table=grouping.rename(grouping.parse(source),p,mirror=mirror,swap=swap)
                if table[0] not in ('---','1LB'):continue
                mask=grouping.defined_mask(table)
                part=tuple(t for i,t in enumerate(table) if mask>>i&1)
                result.setdefault(mask,{}).setdefault(part,(source,p,mirror))
    return sorted(result.items(),key=lambda kv:(-kv[0].bit_count(),kv[0]))


def lookup(index,machine):
    table=grouping.parse(machine);available=grouping.defined_mask(table)
    for mask,part in index:
        if mask&~available:continue
        hit=part.get(tuple(t for i,t in enumerate(table) if mask>>i&1))
        if hit:return hit
    return None


def select(config,machines,build,fuel):
    reps=ROOT/'build/grouping/nonblank.representatives.txt'
    survivor_path=ROOT/'build/advanced/full/not-accepted.txt'
    representatives=reps.read_text().splitlines();survivors=set(survivor_path.read_text().splitlines())
    plain=patterns(machines,False);swapped=patterns(machines,True)
    candidates={};covered=0
    for m in representatives:
        if lookup(plain,m):covered+=1;continue
        hit=lookup(swapped,m)
        if hit:candidates[m]=hit
    build.mkdir(parents=True,exist_ok=True)
    candidate_path=build/'candidates.txt';candidate_path.write_text('\n'.join(candidates)+'\n')
    binary=build/'conjugate_probe'
    subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'tools/conjugate_probe.cpp'),'-o',str(binary)],check=True)
    probe=build/'probe.tsv'
    with probe.open('w') as out:subprocess.run([str(binary),str(fuel),str(candidate_path)],stdout=out,check=True)
    rows=[]
    with probe.open() as f:
        for r in csv.DictReader(f,delimiter='\t'):
            if r['status']!='match':continue
            m=r['machine'];source,p,mirror=candidates[m]
            inverse='P'+''.join(str(p.index(i)) for i in (1,2,3))
            rows.append([m,source,inverse,mirror,int(r['target_boot']),int(r['source_boot']),m in survivors])
    rows.sort()
    return dict(description='Untrusted two-prefix conjugacy witnesses, exact-simulated and replayed in Coq; these rows are canonical cores, not their symbol images.',
                source_inventory_sha256=inventory_hash(machines),source_bound=config['source_bound'],output_bound=config['output_bound'],
                selection=dict(fuel=fuel,canonical_cores=len(representatives),baseline_search_survivors=len(survivors),
                               directly_covered_canonical_cores=covered,table_candidates=len(candidates),
                               table_candidates_in_survivors=sum(m in survivors for m in candidates),
                               representative_sha256=digest(reps),baseline_survivor_sha256=digest(survivor_path)),
                columns=['machine','source','permutation','mirrored','destination_boot','source_boot','baseline_survivor'],rows=rows)


HEADER='''(** GENERATED by four/tools/check_conjugate_batch.py. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard
  Pipeline Symmetry FamilyTransport FamilyIndex ConjugateTransport IndexedConjugate.
Import ListNotations.
'''


def generate(config,machines,rows,build,namespace):
    bs=config['source_bound'];out=config['output_bound'];paths=[]
    body=HEADER+'\n'.join('Require Import '+s['module']+'.' for s in config['sources'])+'\n'
    boards=[]
    for i,s in enumerate(config['sources']):
        prefix=s['module']+'.';board=prefix+s['board'];boards.append(board);b=s['bound']
        body+=f'''Lemma source_{i}_strong : StrongBoard {bs}%N {bs}%N {board}.
Proof.
  eapply (strong_board_weaken {b}%N {b}%N {bs}%N {bs}%N).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - intros tm Hin. split.
    + exact ({prefix+s['nonhalt']} tm Hin).
    + apply ({prefix+s['small_sound']} tm Hin tm). intros q s; right; reflexivity.
Qed.
'''
    proof=f'source_{len(boards)-1}_strong'
    for i in reversed(range(len(boards)-1)):proof=f'(strong_board_app _ _ _ _ source_{i}_strong {proof})'
    body+=f'''Definition source_board : list TM := {' ++ '.join(boards)}.
Lemma source_board_strong : StrongBoard {bs}%N {bs}%N source_board.
Proof. exact {proof}. Qed.
Example source_board_count : N.of_nat (length source_board)={len(machines)}%N.
Proof. vm_compute. reflexivity. Qed.
'''
    p=build/'Sources.v';p.write_text(body);paths.append(p)
    shards=[]
    for offset in range(0,len(rows),SHARD_SIZE):
        entries=[]
        for m,source,p,mirror,destination,origin,_ in rows[offset:offset+SHARD_SIZE]:
            table='['+';'.join(map(str,codes(m)))+']'
            entries.append(f'indexed_conjugate_row {table} {key(source)}%positive {p} {str(mirror).lower()} {destination} {origin}')
        body=HEADER+f'From {namespace} Require Import Sources.\n'
        body+='Definition rows : list IndexedConjugateRow := [\n'+';\n'.join(entries)+'].\n'
        body+=f'''Lemma checked : forallb (indexed_conjugate_check {bs}%N {bs}%N {out}%N {out}%N (family_index source_board)) rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := map indexed_conjugate_tm rows.
Lemma strong : StrongBoard {out}%N {out}%N board.
Proof. exact (indexed_conjugate_batch_sound {bs}%N {bs}%N {out}%N {out}%N source_board rows source_board_strong checked). Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
'''
        p=build/f'Rows{offset//SHARD_SIZE:04}.v';p.write_text(body);paths.append(p);shards.append(p.stem)
    body=HEADER+f'From {namespace} Require Import '+ ' '.join(shards)+'.\n'
    board=' ++ '.join(s+'.board' for s in shards) or '[]'
    proof=shards[-1]+'.strong'
    for s in reversed(shards[:-1]):proof=f'(strong_board_app _ _ _ _ {s}.strong {proof})'
    pending='\n'.join('  rewrite '+s+'.pending_checked.' for s in shards)
    body+=f'''Definition board : list TM := {board}.
Lemma strong : StrongBoard {out}%N {out}%N board.
Proof. exact {proof}. Qed.
Lemma small_sound : BoardSound {out}%N {out}%N board.
Proof. apply strong_board_completions, strong. Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof. intros family H; exact (proj1 (strong family H)). Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
  intros family Hin tm Hle. eapply (bounds_weaken {out}%N {out}%N scoreN scoreN).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (small_sound family Hin tm Hle).
Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof.
  unfold board. repeat rewrite forallb_app.
{pending}
  reflexivity.
Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, Bounds scoreN scoreN tm \\/ pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ was_pending sound). Qed.
Example board_count : N.of_nat (length board)={len(rows)}%N.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions discharged.
'''
    p=build/'ConjugateAll.v';p.write_text(body);paths.append(p)
    return paths


def compact(data):
    return '{\n'+',\n'.join('  '+json.dumps(k)+': '+(
        '[\n'+',\n'.join('    '+json.dumps(r,separators=(',',':')) for r in v)+'\n  ]'
        if k=='rows' else json.dumps(v,sort_keys=True)) for k,v in data.items())+'\n}\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config',type=Path,default=DEFAULT_CONFIG)
    parser.add_argument('--input',type=Path,default=DEFAULT_INPUT)
    parser.add_argument('--name',default='r000')
    parser.add_argument('--select',action='store_true');parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--fuel',type=int,default=4096)
    parser.add_argument('--cache',action='append',type=Path,default=[])
    parser.add_argument('--timeout',type=int,default=36000)
    args=parser.parse_args()
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name):raise ValueError('Invalid batch name')
    if args.select and not args.refresh:raise ValueError('--select requires --refresh')
    namespace='BBB24Conjugate'+args.name.capitalize();build=ROOT/'build/conjugate'/args.name;build.mkdir(parents=True,exist_ok=True)
    config,machines,inputs,loadpaths=sources(args.config)
    data=select(config,machines,build,args.fuel) if args.select else json.loads(args.input.read_text())
    validate(data,machines,config)
    if args.select:args.input.write_text(compact(data))
    inputs[str(args.input.relative_to(ROOT))]=digest(args.input)
    inputs['tools/check_conjugate_batch.py']=digest(__file__)
    inputs['tools/conjugate_probe.cpp']=digest(ROOT/'tools/conjugate_probe.cpp')
    inputs['tools/kernel_audit_cache.py']=digest(ROOT/'tools/kernel_audit_cache.py')
    paths=generate(config,machines,data['rows'],build,namespace)
    loadpaths.append((build,namespace));loadargs=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    with (build/'compile.log').open('w') as log:
        for p in paths:
            print('Compiling '+p.name,flush=True)
            subprocess.run(['coqc','-native-compiler','no',*loadargs,str(p)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    receipt_path,audit_log=fresh_paths(build)
    receipt=audit([namespace+'.ConjugateAll'],[paths[-1]],loadpaths,receipt_path,audit_log,cache=args.cache,timeout=args.timeout)
    if any(digest(ROOT/p)!=h for p,h in inputs.items()):raise ValueError('Pinned input changed during checking')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(data['columns']+['state_bound','instruction_bound','census_linked'])
    writer.writerows(r+[config['output_bound'],config['output_bound'],'yes'] for r in data['rows'])
    descriptor=dict(module=namespace+'.ConjugateAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',
                    bound=config['output_bound'],proof_source=str(paths[-1].relative_to(ROOT)),
                    load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=n) for p,n in loadpaths if n!='BBB24'],
                    machine_inputs=[dict(path=str(args.input.relative_to(ROOT)),format='json_columns')],
                    audited_report=f'research/conjugate-{args.name}-summary.json')
    report=dict(canonical_cores=len(data['rows']),baseline_search_survivors=sum(r[-1] for r in data['rows']),
                symbol_images_included=False,selection=data['selection'],source_board_entries=len(machines),source_distinct_ids=len(set(machines)),
                max_destination_boot=max(r[4] for r in data['rows']),max_source_boot=max(r[5] for r in data['rows']),
                descriptor=descriptor,validation='coqc plus '+receipt['kind']+' coqchk',
                audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),inputs=inputs,
                ledger_sha256=hashlib.sha256(ledger.getvalue().encode()).hexdigest(),
                proof_source_sha256={p.name:digest(p) for p in paths},
                audit_cache_note='Local receipts pin source, object, runtime and transitive dependencies. A final recursive combined audit is required before publishing a new census total.')
    report_path=ROOT/f'research/conjugate-{args.name}-summary.json';ledger_path=ROOT/f'research/conjugate-{args.name}.tsv'
    if args.refresh:
        ledger_path.write_text(ledger.getvalue());report_path.write_text(json.dumps(report,indent=2)+'\n')
    else:
        previous=json.loads(report_path.read_text())
        for k in ('canonical_cores','baseline_search_survivors','inputs','ledger_sha256','proof_source_sha256'):
            if previous[k]!=report[k]:raise ValueError('Replayed evidence changed: '+k)
        if ledger_path.read_text()!=ledger.getvalue():raise ValueError('Ledger changed')
    print(json.dumps({k:report[k] for k in ('canonical_cores','baseline_search_survivors','validation')}))


if __name__=='__main__':main()
