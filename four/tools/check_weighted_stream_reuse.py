"""Replay recurring-template reuse from an immutable weighted source registry.

Matching indexes compact live-instruction tables and lazily reads source graphs.
Proof files group sixteen templates per module; generated proofs stay ignored.
Default replay uses the tracked compact target references. Only --select reads
the large survivor list. Each target passes the separate-table suffix checker,
regardless of whether its source registry is still a candidate snapshot.
"""
import argparse
from collections import defaultdict
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess

import group_families as grouping
from generate_pipeline_examples import codes
from kernel_audit_cache import audit,digest,fresh_paths
from weighted_codec_v2 import bundle_decode,unpack
from weighted_render import HEADER as CERT_HEADER,render
from weighted_reuse_search import transform
from weighted_template_index import header,select

ROOT=Path(__file__).resolve().parents[1]
COMMON=CERT_HEADER+'''From BBB24 Require Import Bootstrap Closeout CertifiedBoard Pipeline
  FamilyTransport WeightedReuse WeightedSuffix.
'''
TEMPLATES_PER_PART=16


def sources(registry_path):
    registry=json.loads(registry_path.read_text());all_rows=[]
    inputs={str(registry_path.resolve().relative_to(ROOT)):digest(registry_path)}
    for entry in registry['bundles']:
        path=ROOT/entry['path']
        if digest(path)!=entry['sha256']:raise ValueError('Frozen source bundle hash changed')
        rows=bundle_decode(path.read_text())
        if len(rows)!=entry['rows']:raise ValueError('Source bundle row count changed')
        inputs[entry['path']]=digest(path);all_rows+=rows
    if len(all_rows)!=registry['rows']:raise ValueError('Source registry row count changed')
    weighted=[r for r in all_rows if r.get('kind')=='weighted' or 'graph' in r]
    if not weighted:raise ValueError('Registry contains no weighted templates')
    return weighted,{header(r)['machine'] for r in all_rows},inputs


def excluded_ids(path):
    if path.suffix=='.tsv':
        with path.open() as f:return {r['machine'] for r in csv.DictReader(f,delimiter='\t')}
    data=json.loads(path.read_text());rows=data['rows']
    if 'columns' in data:
        index=data['columns'].index('machine');return {r[index] for r in rows}
    return {r['machine'] if isinstance(r,dict) else r for r in rows}


def groups(rows):
    grouped=defaultdict(list)
    for row in rows:grouped[tuple(row[1:4])].append(row)
    return [part for group in grouped.values() for start in range(0,len(group),128)
            for part in [group[start:start+128]]]


def template(raw,rows,name,proof):
    source=raw if 'graph' in raw else unpack(raw)
    _,_,permutation,swap,_,_=rows[0]
    p=(0,)+tuple(map(int,permutation));changed=transform(source,p,swap)
    prefix=render(changed)
    if not prefix.startswith(CERT_HEADER):raise ValueError('Certificate renderer header changed')
    body=prefix[len(CERT_HEADER):].split('Definition family:TM:=',1)[0]
    g=source['graph'];loop=grouping.render(grouping.rename(grouping.parse(g['machine']),p,mirror=bool(g['mirror']),swap=swap))
    body+='Definition source := machine_of_codes ['+';'.join(map(str,codes(loop)))+'].\n'
    body+='Definition rows : list WeightedReuseRow := [\n'+';\n'.join(
        'weighted_reuse_row ['+';'.join(map(str,codes(m)))+f'] {str(mirror).lower()} {boot}'
        for m,_,_,_,mirror,boot in rows)+'].\n'
    if proof:
        body+=f'''Lemma checked : forallb (weighted_suffix_row_check 4096%N 4096%N source {g['n']} nodes certificate) rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := map reuse_tm rows.
Lemma strong : StrongBoard 4096%N 4096%N board.
Proof. exact (weighted_suffix_batch_sound _ _ _ _ _ _ _ checked). Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
'''
    return f'Module {name}.\n'+body+f'End {name}.\n',g['n']


def join_board(names):
    proof=names[-1]+'.strong'
    for name in reversed(names[:-1]):proof=f'(strong_board_app _ _ _ _ {name}.strong {proof})'
    text='Definition board : list TM := '+' ++ '.join(n+'.board' for n in names)+'.\n'
    text+=f'''Lemma strong : StrongBoard 4096%N 4096%N board.
Proof. exact {proof}. Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof.
  unfold board. repeat rewrite forallb_app.
'''
    return text+'\n'.join('  rewrite '+n+'.pending_checked.' for n in names)+'\n  reflexivity.\nQed.\n'


def generate(sources,rows,build,namespace,proof):
    paths=[];chunks=groups(rows);counts=[]
    for start in range(0,len(chunks),TEMPLATES_PER_PART):
        body=COMMON;names=[];checks=[];count=0
        for i,chunk in enumerate(chunks[start:start+TEMPLATES_PER_PART]):
            name=f'T{i:03}';text,width=template(sources[chunk[0][1]],chunk,name,proof)
            body+=text;names.append(name);count+=len(chunk)
            checks.append(f'map (weighted_suffix_row_check 4096%N 4096%N {name}.source {width} {name}.nodes {name}.certificate) {name}.rows')
        if proof:body+=join_board(names)
        else:body+='Eval vm_compute in ('+' ++ '.join('('+c+')' for c in checks)+').\n'
        path=build/f'Part{start//TEMPLATES_PER_PART:04}.v';path.write_text(body);paths.append(path);counts.append(count)
    if not proof:return paths,counts
    names=[p.stem for p in paths]
    body=COMMON+f'From {namespace} Require Import '+' '.join(names)+'.\n'+join_board(names)
    body+=r'''Lemma small_sound : BoardSound 4096%N 4096%N board.
Proof. apply strong_board_completions, strong. Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof. intros family H; exact (proj1 (strong family H)). Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
  intros family Hin tm Hle. eapply (bounds_weaken 4096%N 4096%N scoreN scoreN).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (small_sound family Hin tm Hle).
Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, Bounds scoreN scoreN tm \/ pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ Bounds scoreN scoreN tm /\ ~ pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ was_pending sound). Qed.
'''
    body+=f'''Example board_count : N.of_nat (length board)={len(rows)}%N.
Proof. vm_compute. reflexivity. Qed.
'''
    path=build/'WeightedStreamAll.v';path.write_text(body);paths.append(path)
    return paths,counts


def probe(sources,rows,build,namespace,timeout):
    directory=build/'probe';directory.mkdir(exist_ok=True)
    paths,counts=generate(sources,rows,directory,namespace,False);selected=[];offset=0
    for path,count in zip(paths,counts):
        result=subprocess.run(['coqc','-native-compiler','no','-Q',str(ROOT/'theories'),'BBB24',str(path)],capture_output=True,text=True,check=True,timeout=timeout)
        path.with_suffix('.log').write_text(result.stdout+result.stderr)
        match=re.search(r'=\s*\[([a-z;\s]*)\]\s*:\s*list bool',result.stdout)
        if not match:raise ValueError('Cannot parse full-checker selection')
        values=[v.strip() for v in match[1].split(';') if v.strip()]
        if len(values)!=count or any(v not in {'true','false'} for v in values):raise ValueError('Malformed selector result')
        selected.extend(row for row,value in zip(rows[offset:offset+count],values) if value=='true');offset+=count
        print('Probed '+path.name,flush=True)
    if offset!=len(rows):raise ValueError('Probe omitted a row')
    return selected


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry',type=Path,required=True);parser.add_argument('--name',required=True)
    parser.add_argument('--select',action='store_true');parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--exclude-input',type=Path,action='append',default=[])
    parser.add_argument('--cache',type=Path,action='append',default=[])
    parser.add_argument('--targets',type=Path,default=ROOT/'build/advanced/full/not-accepted.txt',
                        help='Selection-only target inventory; default is the frozen old survivor cohort')
    parser.add_argument('--limit',type=int,default=0);parser.add_argument('--timeout',type=int,default=36000)
    args=parser.parse_args()
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name):raise ValueError('Invalid batch name')
    if args.select and not args.refresh:raise ValueError('--select requires --refresh')
    if args.limit<0:raise ValueError('Invalid selection limit')
    build=ROOT/'build/weighted-stream'/args.name;build.mkdir(parents=True,exist_ok=True)
    directory=ROOT/'research/weighted-stream-reuse';directory.mkdir(exist_ok=True)
    input_path=directory/(args.name+'-input.json');report_path=directory/(args.name+'-summary.json');ledger_path=directory/(args.name+'.tsv')
    namespace='BBB24WeightedStream'+args.name.capitalize();pool,source_ids,inputs=sources(args.registry)
    if args.select:
        baseline=args.targets;excluded=set(source_ids);excluded_hashes={}
        for path in args.exclude_input:
            excluded|=excluded_ids(path);excluded_hashes[str(path.resolve().relative_to(ROOT))]=digest(path)
        rows,stats=select(pool,baseline.read_text().splitlines(),excluded=excluded)
        if args.limit:rows=rows[:args.limit]
        rows.sort(key=lambda r:(tuple(r[1:4]),r[0]));stats['probe_candidates']=len(rows)
        if not rows:raise ValueError('No selected targets; no proof board published')
        rows=probe(pool,rows,build,namespace,args.timeout);stats['checker_selected_cores']=len(rows)
        if not rows:raise ValueError('No full-checker successes; no proof board published')
        data=dict(description='Targets entering separate-table weighted closures; compact references select untrusted certificates, and every target is kernel checked.',
                  registry_sha256=digest(args.registry),baseline_survivor_sha256=digest(baseline),exclusion_inputs_sha256=excluded_hashes,selection=stats,
                  columns=['machine','source_certificate','permutation','state_swap','mirrored','boot'],rows=rows)
        if baseline.resolve()!=(ROOT/'build/advanced/full/not-accepted.txt').resolve():
            data['selection_target_inventory']=str(baseline.resolve().relative_to(ROOT))
        text='{\n'+',\n'.join('  '+json.dumps(k)+': '+('[\n'+',\n'.join('    '+json.dumps(r,separators=(',',':')) for r in v)+'\n  ]' if k=='rows' else json.dumps(v,sort_keys=True)) for k,v in data.items())+'\n}\n'
        if report_path.exists() and input_path.read_text()!=text:raise ValueError('Frozen batch selection changed; choose a new name')
        input_path.write_text(text)
    else:data=json.loads(input_path.read_text());rows=data['rows']
    if data['registry_sha256']!=digest(args.registry):raise ValueError('Source registry changed')
    if not rows or len({r[0] for r in rows})!=len(rows):raise ValueError('Empty or duplicate target inventory')
    for row in rows:
        if len(row)!=6:raise ValueError('Malformed target reference')
        m,index,p,swap,mirror,boot=row;codes(m)
        if type(index)is not int or not 0<=index<len(pool):raise ValueError('Invalid template index')
        if p not in {'123','132','213','231','312','321'}:raise ValueError('Invalid symbol permutation')
        if type(swap)is not bool or type(mirror)is not bool:raise ValueError('Invalid transformation flags')
        if type(boot)is not int or not 0<=boot<=4096:raise ValueError('Invalid boot')
    if rows!=sorted(rows,key=lambda r:(tuple(r[1:4]),r[0])):raise ValueError('Input differs from board order')
    for path in [input_path,Path(__file__)]+[ROOT/'tools'/name for name in ('weighted_template_index.py','weighted_reuse_search.py','weighted_render.py','weighted_codec_v2.py','kernel_audit_cache.py')]:
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    paths,_=generate(pool,rows,build,namespace,True);loadpaths=[(ROOT/'theories','BBB24'),(build,namespace)]
    flags=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    with (build/'compile.log').open('w') as log:
        for path in paths:
            subprocess.run(['coqc','-native-compiler','no',*flags,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
            print('Compiled '+path.name,flush=True)
    receipt_path,log=fresh_paths(build)
    receipt=audit([namespace+'.WeightedStreamAll'],[paths[-1]],loadpaths,receipt_path,log,cache=args.cache,timeout=args.timeout)
    if any(digest(ROOT/p)!=h for p,h in inputs.items()):raise ValueError('Pinned source changed during replay')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(data['columns']+['state_bound','instruction_bound','census_linked'])
    writer.writerows(r+[4096,4096,'yes'] for r in rows)
    descriptor=dict(module=namespace+'.WeightedStreamAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',bound=4096,
                    proof_source=str(paths[-1].relative_to(ROOT)),load_paths=[dict(path=str(build.relative_to(ROOT)),namespace=namespace)],
                    machine_inputs=[dict(path=str(input_path.relative_to(ROOT)),format='json_columns')],audited_report=str(report_path.relative_to(ROOT)))
    report=dict(canonical_cores=len(rows),source_weighted_templates=len(pool),descriptor=descriptor,selection=data['selection'],
                validation='coqc plus '+receipt['kind']+' coqchk',inputs=inputs,audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),
                ledger_sha256=hashlib.sha256(ledger.getvalue().encode()).hexdigest(),proof_source_sha256={p.name:digest(p) for p in paths},
                publication_note='Include this exact board in the final recursive combined audit before publishing an updated census total.')
    if args.refresh:report_path.write_text(json.dumps(report,indent=2)+'\n');ledger_path.write_text(ledger.getvalue())
    else:
        old=json.loads(report_path.read_text())
        for k in ('canonical_cores','inputs','ledger_sha256','proof_source_sha256'):
            if old[k]!=report[k]:raise ValueError('Replay changed: '+k)
        if ledger_path.read_text()!=ledger.getvalue():raise ValueError('Ledger changed')
    print(json.dumps({k:report[k] for k in ('canonical_cores','source_weighted_templates','validation')}))


if __name__=='__main__':main()
