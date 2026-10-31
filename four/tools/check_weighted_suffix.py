"""Replay target boots into weighted closures over a separate source table.

The source table and target need agree only on the supplied closure's live
instruction slots. Every table-agreement, closure, ranking and prefix condition
is checked by WeightedSuffix; candidate selection carries no trusted evidence.
Default reproduction uses compact tracked references and certificate bundles.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess

import check_weighted_reuse as direct
import group_families as grouping
from generate_pipeline_examples import codes
from kernel_audit_cache import audit,digest,fresh_paths
from weighted_codec_v2 import bundle_decode,unpack
from weighted_reuse_search import select

ROOT=Path(__file__).resolve().parents[1]


def generate(sources,rows,build,namespace):
    direct.BUILD=build;direct.NAMESPACE=namespace
    paths=direct.generate(sources,rows)
    offset=0
    for path in paths[:-1]:
        text=path.read_text();count=text.count('weighted_reuse_row ')
        _,index,p,swap,_,_=rows[offset]
        if any(tuple(r[1:4])!=(index,p,swap) for r in rows[offset:offset+count]):
            raise ValueError('Mixed certificate templates in one shard')
        source=sources[index]['graph']
        table=grouping.render(grouping.rename(grouping.parse(source['machine']),
              (0,)+tuple(map(int,p)),mirror=bool(source['mirror']),swap=swap))
        definition='Definition suffix_source := machine_of_codes ['+';'.join(map(str,codes(table)))+'].\n'
        text='From BBB24 Require Import WeightedSuffix.\n'+text
        text=text.replace('Definition rows :',definition+'Definition rows :',1)
        old='weighted_reuse_check 4096%N 4096%N '
        if text.count(old)!=1:raise ValueError('Unexpected checker template')
        text=text.replace(old,'weighted_suffix_row_check 4096%N 4096%N suffix_source ',1)
        old='weighted_reuse_batch_sound _ _ _ _ _ _ checked'
        if text.count(old)!=1:raise ValueError('Unexpected soundness template')
        text=text.replace(old,'weighted_suffix_batch_sound _ _ _ _ _ _ _ checked',1)
        path.write_text(text);offset+=count
    if offset!=len(rows):raise ValueError('Generated board omitted a row')
    new=build/'WeightedSuffixAll.v';paths[-1].rename(new);paths[-1]=new
    return paths


def probe(sources,rows,build,namespace,timeout):
    paths=generate(sources,rows,build,namespace)[:-1]
    directory=build/'probe';directory.mkdir(exist_ok=True);selected=[];offset=0
    for i,path in enumerate(paths):
        prefix,rest=path.read_text().split('Lemma checked : forallb ',1)
        checker=rest.split(' rows=true.',1)[0];count=prefix.count('weighted_reuse_row ')
        target=directory/path.name;target.write_text(prefix+'Eval vm_compute in map '+checker+' rows.\n')
        result=subprocess.run(['coqc','-native-compiler','no','-Q',str(ROOT/'theories'),'BBB24',str(target)],
                              capture_output=True,text=True,check=True,timeout=timeout)
        target.with_suffix('.log').write_text(result.stdout+result.stderr)
        match=re.search(r'=\s*\[([a-z;\s]*)\]\s*:\s*list bool',result.stdout)
        if not match:raise ValueError('Cannot parse suffix selection result')
        values=[v.strip() for v in match[1].split(';') if v.strip()]
        if len(values)!=count or any(v not in {'true','false'} for v in values):raise ValueError('Malformed result')
        selected.extend(r for r,v in zip(rows[offset:offset+count],values) if v=='true');offset+=count
        if i%10==0:print(f'Probed {i+1}/{len(paths)} suffix templates',flush=True)
    if offset!=len(rows):raise ValueError('Selection omitted a row')
    return selected


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name',default='pilot')
    parser.add_argument('--certificates',type=Path,default=ROOT/'research/weighted-pilot-certificates.jsonl')
    parser.add_argument('--select',action='store_true');parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--cache',action='append',type=Path,default=[])
    parser.add_argument('--exclude-input',action='append',type=Path,default=[],
                        help='During --select, omit IDs listed in an earlier compact input; affects selection only')
    parser.add_argument('--timeout',type=int,default=36000)
    args=parser.parse_args()
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name):raise ValueError('Invalid batch name')
    if args.select and not args.refresh:raise ValueError('--select requires --refresh')
    stem='weighted-suffix-'+args.name;namespace='BBB24WeightedSuffix'+args.name.capitalize()
    build=ROOT/'build/weighted-suffix'/args.name;build.mkdir(parents=True,exist_ok=True)
    input_path=ROOT/f'research/{stem}-input.json';source_path=args.certificates.resolve()
    sources=[r if 'graph' in r else unpack(r) for r in bundle_decode(source_path.read_text())
             if 'graph' in r or r.get('kind')=='weighted']
    if args.select:
        baseline=ROOT/'build/advanced/full/not-accepted.txt'
        rows,stats=select(sources,baseline.read_text().splitlines())
        excluded=set();exclusion_hashes={}
        for path in args.exclude_input:
            old=json.loads(path.read_text());column=old['columns'].index('machine')
            excluded.update(row[column] for row in old['rows'])
            exclusion_hashes[str(path.resolve().relative_to(ROOT))]=digest(path)
        stats['excluded_previously_selected_cores']=sum(r[0] in excluded for r in rows)
        rows=[r for r in rows if r[0] not in excluded]
        rows.sort(key=lambda r:(tuple(r[1:4]),r[0]))
        rows=probe(sources,rows,build,namespace,args.timeout);stats['checker_selected_cores']=len(rows)
        data=dict(description='Canonical target cores with checked boots into separate-table weighted closures; every live-instruction agreement is replayed.',
                  source_certificate_sha256=digest(source_path),baseline_survivor_sha256=digest(baseline),exclusion_inputs_sha256=exclusion_hashes,selection=stats,
                  columns=['machine','source_certificate','permutation','state_swap','mirrored','boot'],rows=rows)
        text='{\n'+',\n'.join('  '+json.dumps(k)+': '+('[\n'+',\n'.join('    '+json.dumps(r,separators=(',',':')) for r in v)+'\n  ]' if k=='rows' else json.dumps(v,sort_keys=True)) for k,v in data.items())+'\n}\n'
        input_path.write_text(text)
    else:data=json.loads(input_path.read_text());rows=data['rows']
    if data['source_certificate_sha256']!=digest(source_path):raise ValueError('Source certificate inventory changed')
    if not rows or len({r[0] for r in rows})!=len(rows):raise ValueError('Empty or duplicate target inventory')
    for row in rows:
        if len(row)!=6:raise ValueError('Malformed suffix row')
        m,index,p,swap,mirror,boot=row;codes(m)
        if type(index)is not int or not 0<=index<len(sources):raise ValueError('Invalid source index')
        if p not in {'123','132','213','231','312','321'}:raise ValueError('Invalid symbol permutation')
        if type(swap)is not bool or type(mirror)is not bool:raise ValueError('Invalid transformation flags')
        if type(boot)is not int or not 0<=boot<=4096:raise ValueError('Invalid boot bound')
    if rows!=sorted(rows,key=lambda r:(tuple(r[1:4]),r[0])):raise ValueError('Input is not in exact board order')
    pinned=[source_path,input_path,Path(__file__)]+[ROOT/'tools'/name for name in
        ('check_weighted_reuse.py','weighted_reuse_search.py','weighted_render.py','weighted_codec_v2.py','kernel_audit_cache.py')]
    pinned += [ROOT/'theories/WeightedSuffix.v',ROOT/'theories/WeightedSuffixRegression.v']
    inputs={str(p.resolve().relative_to(ROOT)):digest(p) for p in pinned}
    paths=generate(sources,rows,build,namespace);loadpaths=[(ROOT/'theories','BBB24'),(build,namespace)]
    loadargs=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    with (build/'compile.log').open('w') as log:
        for i,path in enumerate(paths):
            subprocess.run(['coqc','-native-compiler','no',*loadargs,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
            if i%10==0:print(f'Compiled {i+1}/{len(paths)} suffix modules',flush=True)
    receipt_path,audit_log=fresh_paths(build)
    receipt=audit([namespace+'.WeightedSuffixAll','BBB24.WeightedSuffixRegression'],
                  [paths[-1],ROOT/'theories/WeightedSuffixRegression.v'],loadpaths,receipt_path,audit_log,cache=args.cache,timeout=args.timeout)
    if any(digest(ROOT/p)!=h for p,h in inputs.items()):raise ValueError('Pinned input changed during replay')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(data['columns']+['state_bound','instruction_bound','census_linked'])
    writer.writerows(r+[4096,4096,'yes'] for r in rows)
    descriptor=dict(module=namespace+'.WeightedSuffixAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',bound=4096,
                    proof_source=str(paths[-1].relative_to(ROOT)),load_paths=[dict(path=str(build.relative_to(ROOT)),namespace=namespace)],
                    machine_inputs=[dict(path=str(input_path.relative_to(ROOT)),format='json_columns')],audited_report=f'research/{stem}-summary.json')
    report=dict(canonical_cores=len(rows),symbol_images_included=False,selection=data['selection'],descriptor=descriptor,
                validation='coqc plus '+receipt['kind']+' coqchk',inputs=inputs,audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),
                ledger_sha256=hashlib.sha256(ledger.getvalue().encode()).hexdigest(),proof_source_sha256={p.name:digest(p) for p in paths},
                note='Incremental receipts must be included in a final recursive combined audit before publishing an updated census total.')
    report_path=ROOT/f'research/{stem}-summary.json';ledger_path=ROOT/f'research/{stem}.tsv'
    if args.refresh:report_path.write_text(json.dumps(report,indent=2)+'\n');ledger_path.write_text(ledger.getvalue())
    else:
        old=json.loads(report_path.read_text())
        for k in ('canonical_cores','inputs','ledger_sha256','proof_source_sha256'):
            if old[k]!=report[k]:raise ValueError('Replay changed: '+k)
        if ledger_path.read_text()!=ledger.getvalue():raise ValueError('Ledger changed')
    print(json.dumps({k:report[k] for k in ('canonical_cores','validation')}))


if __name__=='__main__':main()
