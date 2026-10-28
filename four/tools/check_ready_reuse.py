"""Reuse already proved weighted tails through compact source-module references.

Default replay needs only tracked inventories, the reproduced source proof
modules, and the generic ReadyReuse theory. Selection diagnostics are optional
inputs only when creating a new inventory. Compiled-only reports explicitly
claim zero newly audited families; a combined campaign audit can discharge
their exact imported source closure once, without repeating source rankings.
"""
import argparse
import collections
import csv
import io
import json
from pathlib import Path
import re
import resource
import subprocess
import time

import check_weighted_stream_reuse as base
from generate_pipeline_examples import codes
from kernel_audit_cache import audit,digest,fresh_paths,snapshot
from weighted_codec_v2 import bundle_decode

ROOT=Path(__file__).resolve().parents[1]
COMMON=base.COMMON+'From BBB24 Require Import ReadyReuse WeightedTail Symmetry.\n'


def source_inventory(registries):
    sources=[];paths=[(ROOT/'theories','BBB24')];pins={}
    for registry_path in registries:
        registry_path=ROOT/registry_path;report_path=registry_path.with_name('check.json')
        registry=json.loads(registry_path.read_text());report=json.loads(report_path.read_text())
        for p in (registry_path,report_path):pins[str(p.relative_to(ROOT))]=digest(p)
        descriptor=report['descriptor'];lp=descriptor['load_paths'][0]
        directory=ROOT/lp['path'];namespace=lp['namespace'];paths.append((directory,namespace))
        packed=[]
        for entry in registry['bundles']:
            path=ROOT/entry['path']
            if digest(path)!=entry['sha256']:raise ValueError('Source bundle changed')
            rows=bundle_decode(path.read_text())
            if len(rows)!=entry['rows']:raise ValueError('Source bundle count changed')
            packed.extend(rows);pins[entry['path']]=digest(path)
        if len(packed)!=registry['rows'] or len(packed)!=len(report['results']):
            raise ValueError('Source result inventory changed')
        seen=collections.Counter()
        for row,result in zip(packed,report['results']):
            if row['machine']!=result['machine'] or row['kind']!=result['kind'] or result['status']!='coq_checked':
                raise ValueError('Source proof ordering or status changed')
            module=result['module']
            if not re.fullmatch(r'Weighted[0-9]+[AB]*',module):raise ValueError('Invalid proof module')
            sub=seen[module];seen[module]+=1
            if row['kind']!='weighted':continue
            path=directory/(module+'.v')
            if digest(path)!=report['artifacts_sha256'][module+'.v']:
                raise ValueError('Source proof text changed')
            pins[str(path.relative_to(ROOT))]=digest(path)
            sources.append(dict(machine=row['machine'],mirror=row['mirror'],n=row['n'],t=row['t'],
                module=namespace+'.'+module,proof=namespace+'.'+module+f'.R{sub:04}'))
    for p in (Path(__file__),Path(base.__file__),ROOT/'tools/weighted_codec_v2.py',
              ROOT/'tools/generate_pipeline_examples.py',ROOT/'theories/ReadyReuse.v',
              ROOT/'tools/kernel_audit_cache.py'):
        pins[str(p.resolve().relative_to(ROOT))]=digest(p)
    return sources,paths,pins


def template(source,rows,name,proof):
    if not proof:raise ValueError('Readiness comes from a source theorem, not a probe')
    ref=source['proof'];machine=f'(mirror_tm {ref}.family)'if source['mirror']else ref+'.family'
    namespace,module=source['module'].rsplit('.',1)
    body=f'From {namespace} Require Import {module}.\nModule {name}.\n'
    body+=f'Definition tail := prepared_tail {machine} {source["n"]} {source["t"]} {ref}.nodes {ref}.certificate.\n'
    body+=f'Lemma ready : wt_ready tail=true.\nProof. exact(graph_prepares_ready_tail _ _ _ _ _ _ _ {ref}.checked). Qed.\n'
    body+='Definition rows:list ReadyReuseRow := [\n'+';\n'.join(
        'ready_reuse_row ['+';'.join(map(str,codes(m)))+f'] P{p} {str(mirror).lower()} {boot}'
        for m,_,p,_,mirror,boot in rows)+'].\n'
    body+='''Lemma checked : forallb(ready_reuse_check 4096%N 4096%N tail)rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board:=map rr_tm rows.
Lemma strong:StrongBoard 4096%N 4096%N board.
Proof. exact(ready_reuse_batch_sound _ _ _ _ ready checked). Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute. reflexivity. Qed.
'''
    return body+f'End {name}.\n',source['n']


def groups(rows):
    result=[];by_source=collections.defaultdict(list)
    for row in rows:by_source[row[1]].append(row)
    for group in by_source.values():
        result.extend(group[start:start+128]for start in range(0,len(group),128))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name',required=True)
    parser.add_argument('--select-candidates',type=Path)
    parser.add_argument('--source-registry',action='append',default=[])
    parser.add_argument('--limit',type=int,default=0)
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--cache',type=Path,action='append',default=[])
    parser.add_argument('--refresh',action='store_true')
    args=parser.parse_args()
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name) or args.limit<0:raise ValueError('Invalid batch parameters')
    directory=ROOT/'research/ready-reuse';directory.mkdir(exist_ok=True)
    build=ROOT/'build/ready-reuse'/args.name;build.mkdir(parents=True,exist_ok=True)
    input_path=directory/(args.name+'-input.json');suffix='summary'if args.audit else'compiled'
    report_path=directory/(args.name+'-'+suffix+'.json');ledger_path=directory/(args.name+'.tsv')
    if args.select_candidates:
        if not args.refresh or not args.source_registry:raise ValueError('New selection requires --refresh and ordered registries')
        rows=json.loads(args.select_candidates.read_text())['matches']
        if args.limit:rows=rows[:args.limit]
        rows=sorted(rows,key=lambda row:(row[1],row[0]))
        data=dict(description='Target boots into already proved weighted source tails; no source ranks are recomputed.',
            source_registries=args.source_registry,selection_sha256=digest(args.select_candidates),
            columns=['machine','source_certificate','permutation','state_swap','mirrored','boot'],rows=rows)
        text=json.dumps(data,indent=2)+'\n'
        if input_path.exists()and input_path.read_text()!=text:raise ValueError('Frozen inventory changed')
        input_path.write_text(text)
    else:data=json.loads(input_path.read_text());rows=data['rows']
    sources,loadpaths,pins=source_inventory(data['source_registries'])
    if not rows or len({r[0]for r in rows})!=len(rows):raise ValueError('Empty or duplicate targets')
    for row in rows:
        if len(row)!=6:raise ValueError('Malformed reference')
        m,index,p,swap,mirror,boot=row;codes(m)
        if type(index)is not int or not 0<=index<len(sources):raise ValueError('Invalid source index')
        if p not in {'123','132','213','231','312','321'}or swap is not False or type(mirror)is not bool:
            raise ValueError('Invalid symmetry')
        if type(boot)is not int or not 0<=boot<=4096:raise ValueError('Invalid boot')
    if rows!=sorted(rows,key=lambda r:(r[1],r[0])):raise ValueError('Board order changed')
    pins[str(input_path.relative_to(ROOT))]=digest(input_path)
    namespace='BBB24ReadyReuse'+args.name.capitalize()
    base.COMMON=COMMON;base.template=template;base.groups=groups
    proofs,_=base.generate(sources,rows,build,namespace,True)
    aggregate=build/'ReadyReuseAll.v';proofs[-1].replace(aggregate);proofs[-1]=aggregate
    loadpaths.append((build,namespace));flags=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
    with(build/'compile.log').open('w')as log:
        for path in proofs:
            subprocess.run(['coqc','-native-compiler','no',*flags,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True)
            print('Compiled '+path.name,flush=True)
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    timing=dict(wall_seconds=time.monotonic()-start,
        cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime)
    descriptor=dict(module=namespace+'.ReadyReuseAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',
        was_pending='was_pending',bound=4096,proof_source=str(aggregate.relative_to(ROOT)),
        load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=n)for p,n in loadpaths[1:]],
        machine_inputs=[dict(path=str(input_path.relative_to(ROOT)),format='json_columns')],audited_report=str(report_path.relative_to(ROOT)))
    report=dict(status='compiled_queued_campaign_audit',compiled_canonical_cores=len(rows),checked_canonical_cores=0,
        descriptor=descriptor,inputs_sha256=pins,proof_source_sha256={p.name:digest(p)for p in proofs},compile=timing,
        note='Source rankings come from imported checked theorems. The final campaign must audit this exact transitive closure before adding an audited census count.')
    if args.audit:
        receipt_path,log=fresh_paths(build)
        receipt=audit([namespace+'.ReadyReuseAll'],[aggregate],loadpaths,receipt_path,log,cache=args.cache)
        report.update(status='kernel_audited',checked_canonical_cores=len(rows),validation='coqc plus '+receipt['kind']+' coqchk',
            audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path))
    else:
        snap=snapshot([aggregate],loadpaths);path=build/'compiled-snapshot.json'
        path.write_text(json.dumps(snap,indent=2,sort_keys=True)+'\n')
        report.update(compiled_snapshot=str(path.relative_to(ROOT)),compiled_snapshot_sha256=digest(path))
    if any(digest(ROOT/p)!=h for p,h in pins.items()):raise ValueError('Source changed during replay')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n');writer.writerow(data['columns']);writer.writerows(rows)
    report['ledger_sha256']=__import__('hashlib').sha256(ledger.getvalue().encode()).hexdigest()
    if args.refresh:report_path.write_text(json.dumps(report,indent=2)+'\n');ledger_path.write_text(ledger.getvalue())
    else:
        old=json.loads(report_path.read_text())
        for key in ('compiled_canonical_cores','inputs_sha256','proof_source_sha256','descriptor','ledger_sha256'):
            if old[key]!=report[key]:raise ValueError('Portable replay changed '+key)
        if ledger_path.read_text()!=ledger.getvalue():raise ValueError('Ledger changed')
        (build/'latest-replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],families=len(rows),compile=timing)),flush=True)


if __name__=='__main__':main()
