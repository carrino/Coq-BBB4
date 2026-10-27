"""Replay shared weighted recurring closures on new tables and finite boots.

Default replay reads the compact tracked target/template references and tracked
weighted certificates. --select additionally needs the ignored survivor list.
The source ranking is only a candidate certificate: wc_graph_check checks it
again for each target. Successful kernel replay proves both bounds, nonhalting,
all completions, and original bootstrap-census membership.
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

from generate_pipeline_examples import codes
from weighted_render import render
from weighted_reuse_search import select, transform
from kernel_audit_cache import audit, digest, fresh_paths
from weighted_codec_v2 import bundle_decode, unpack

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'research/weighted-pilot-certificates.jsonl'
INPUT=ROOT/'research/weighted-reuse-input.json'
BUILD=ROOT/'build/weighted-reuse'
NAMESPACE='BBB24WeightedReuse'
HEADER='''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard CTape Pipeline WeightedReuse FamilyTransport.
Import ListNotations.
'''


def generate(sources,rows):
    grouped=defaultdict(list)
    for r in rows:grouped[tuple(r[1:4])].append(r)
    paths=[]
    for identity,group in grouped.items():
        source,permutation,swap=identity
        transformed=transform(sources[source],(0,)+tuple(map(int,permutation)),swap)
        prefix=render(transformed).split('Definition family:TM:=',1)[0]
        for start in range(0,len(group),128):
            chunk=group[start:start+128]
            body=prefix+HEADER
            entries=[]
            for m,_,_,_,mirror,boot in chunk:
                entries.append('weighted_reuse_row ['+';'.join(map(str,codes(m)))+f'] {str(mirror).lower()} {boot}')
            body+='Definition rows : list WeightedReuseRow := [\n'+';\n'.join(entries)+'].\n'
            body+=f'''Lemma checked : forallb (weighted_reuse_check 4096%N 4096%N {transformed['graph']['n']} nodes certificate) rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := map reuse_tm rows.
Lemma strong : StrongBoard 4096%N 4096%N board.
Proof. exact (weighted_reuse_batch_sound _ _ _ _ _ _ checked). Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
'''
            path=BUILD/f'Template{len(paths):04}.v';path.write_text(body);paths.append(path)
    names=[p.stem for p in paths]
    body=HEADER+'From '+NAMESPACE+' Require Import '+' '.join(names)+'.\n'
    proof=names[-1]+'.strong'
    for name in reversed(names[:-1]):proof=f'(strong_board_app _ _ _ _ {name}.strong {proof})'
    body+='Definition board : list TM := '+' ++ '.join(n+'.board' for n in names)+'.\n'
    body+=f'''Lemma strong : StrongBoard 4096%N 4096%N board.
Proof. exact {proof}. Qed.
Lemma small_sound : BoardSound 4096%N 4096%N board.
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
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof.
  unfold board. repeat rewrite forallb_app.
'''
    body+='\n'.join('  rewrite '+n+'.pending_checked.' for n in names)+'\n  reflexivity.\nQed.\n'
    body+=r'''Lemma was_pending : forall family, In family board -> bootstrap_pending family.
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
Print Assumptions discharged.
'''
    path=BUILD/'WeightedReuseAll.v';path.write_text(body);paths.append(path)
    return paths


def probe_selection(sources,rows,timeout):
    """Computed search only; selected targets receive fresh proof obligations."""
    paths=generate(sources,rows)[:-1];selected=[];offset=0
    probe=BUILD/'probe';probe.mkdir(exist_ok=True)
    for i,path in enumerate(paths):
        text=path.read_text();prefix,rest=text.split('Lemma checked : forallb ',1)
        checker=rest.split(' rows=true.',1)[0]
        count=prefix.count('weighted_reuse_row ')
        target=probe/path.name
        target.write_text(prefix+'Eval vm_compute in map '+checker+' rows.\n')
        result=subprocess.run(['coqc','-native-compiler','no','-Q',str(ROOT/'theories'),'BBB24',str(target)],
                              capture_output=True,text=True,check=True,timeout=timeout)
        target.with_suffix('.log').write_text(result.stdout+result.stderr)
        match=re.search(r'=\s*\[([a-z;\s]*)\]\s*:\s*list bool',result.stdout)
        if not match:raise ValueError('Cannot parse Boolean selection result')
        values=[v.strip() for v in match[1].split(';') if v.strip()]
        if len(values)!=count or any(v not in {'true','false'} for v in values):
            raise ValueError('Malformed selection result')
        selected.extend(row for row,value in zip(rows[offset:offset+count],values) if value=='true')
        offset+=count
        if i%10==0:print(f'Probed {i+1}/{len(paths)} templates',flush=True)
    if offset!=len(rows):raise ValueError('Selection omitted a row')
    return selected


def main():
    global SOURCE, INPUT, BUILD, NAMESPACE
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select',action='store_true');parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--cache',action='append',type=Path,default=[])
    parser.add_argument('--timeout',type=int,default=36000)
    parser.add_argument('--certificates',type=Path,default=SOURCE)
    parser.add_argument('--name',default='pilot')
    args=parser.parse_args()
    if args.select and not args.refresh:raise ValueError('--select requires --refresh')
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name):raise ValueError('Invalid batch name')
    SOURCE=args.certificates.resolve()
    if args.name!='pilot':
        INPUT=ROOT/f'research/weighted-reuse-{args.name}-input.json'
        BUILD=ROOT/'build/weighted-reuse'/args.name
        NAMESPACE='BBB24WeightedReuse'+args.name.capitalize()
    BUILD.mkdir(parents=True,exist_ok=True)
    sources=[r if 'graph' in r else unpack(r) for r in bundle_decode(SOURCE.read_text())
             if 'graph' in r or r.get('kind')=='weighted']
    if args.select:
        path=ROOT/'build/advanced/full/not-accepted.txt'
        rows,stats=select(sources,path.read_text().splitlines())
        rows.sort(key=lambda r:(tuple(r[1:4]),r[0]))
        rows=probe_selection(sources,rows,args.timeout)
        stats['checker_selected_cores']=len(rows)
        data=dict(description='Shared weighted closure candidates; each target and boot is independently replayed. These are canonical cores, not symbol-image counts.',
                  source_certificate_sha256=digest(SOURCE),baseline_survivor_sha256=digest(path),selection=stats,
                  columns=['machine','source_certificate','permutation','state_swap','mirrored','boot'],rows=rows)
        text='{\n'+',\n'.join('  '+json.dumps(k)+': '+('[\n'+',\n'.join('    '+json.dumps(r,separators=(',',':')) for r in v)+'\n  ]' if k=='rows' else json.dumps(v,sort_keys=True)) for k,v in data.items())+'\n}\n'
        INPUT.write_text(text)
    else:data=json.loads(INPUT.read_text());rows=data['rows']
    if data['source_certificate_sha256']!=digest(SOURCE):raise ValueError('Source certificate inventory changed')
    if not rows or len({r[0] for r in rows})!=len(rows):raise ValueError('Empty or duplicate target inventory')
    for row in rows:
        if len(row)!=6:raise ValueError('Malformed reuse row')
        m,source,p,swap,mirror,boot=row;codes(m)
        if type(source) is not int or not 0<=source<len(sources):raise ValueError('Source certificate index out of range')
        if p not in {'123','132','213','231','312','321'}:raise ValueError('Invalid permutation')
        if type(swap) is not bool or type(mirror) is not bool:raise ValueError('Expected Boolean transformation flags')
        if type(boot) is not int or not 0<=boot<=4096:raise ValueError('Invalid boot bound')
    if rows!=sorted(rows,key=lambda r:(tuple(r[1:4]),r[0])):raise ValueError('Input must be in exact board order')
    pinned=[SOURCE,INPUT,Path(__file__),ROOT/'tools/weighted_reuse_search.py',ROOT/'tools/weighted_render.py',ROOT/'tools/weighted_codec_v2.py',ROOT/'tools/kernel_audit_cache.py',ROOT/'theories/WeightedReuse.v']
    inputs={str(p.resolve().relative_to(ROOT)):digest(p) for p in pinned}
    paths=generate(sources,rows);loadpaths=[(ROOT/'theories','BBB24'),(BUILD,NAMESPACE)]
    loadargs=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    with (BUILD/'compile.log').open('w') as log:
        for i,path in enumerate(paths):
            subprocess.run(['coqc','-native-compiler','no',*loadargs,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
            if i%10==0:print(f'Compiled {i+1}/{len(paths)} modules',flush=True)
    receipt_path,audit_log=fresh_paths(BUILD)
    receipt=audit([NAMESPACE+'.WeightedReuseAll'],[paths[-1]],loadpaths,receipt_path,audit_log,cache=args.cache,timeout=args.timeout)
    if any(digest(ROOT/p)!=h for p,h in inputs.items()):raise ValueError('Pinned input changed during checking')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(data['columns']+['state_bound','instruction_bound','census_linked'])
    writer.writerows(r+[4096,4096,'yes'] for r in rows)
    stem='weighted-reuse' if args.name=='pilot' else 'weighted-reuse-'+args.name
    descriptor=dict(module=NAMESPACE+'.WeightedReuseAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',bound=4096,
                    proof_source=str(paths[-1].relative_to(ROOT)),load_paths=[dict(path=str(BUILD.relative_to(ROOT)),namespace=NAMESPACE)],
                    machine_inputs=[dict(path=str(INPUT.relative_to(ROOT)),format='json_columns')],audited_report=f'research/{stem}-summary.json')
    report=dict(canonical_cores=len(rows),symbol_images_included=False,selection=data['selection'],descriptor=descriptor,
                validation='coqc plus '+receipt['kind']+' coqchk',inputs=inputs,audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),
                ledger_sha256=hashlib.sha256(ledger.getvalue().encode()).hexdigest(),proof_source_sha256={p.name:digest(p) for p in paths})
    report_path=ROOT/f'research/{stem}-summary.json';ledger_path=ROOT/f'research/{stem}.tsv'
    if args.refresh:report_path.write_text(json.dumps(report,indent=2)+'\n');ledger_path.write_text(ledger.getvalue())
    else:
        previous=json.loads(report_path.read_text())
        for k in ('canonical_cores','inputs','ledger_sha256','proof_source_sha256'):
            if previous[k]!=report[k]:raise ValueError('Replay changed: '+k)
        if ledger_path.read_text()!=ledger.getvalue():raise ValueError('Ledger changed')
    print(json.dumps({k:report[k] for k in ('canonical_cores','validation')}))


if __name__=='__main__':main()
