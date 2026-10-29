"""Resumable one-CPU weighted search with compact, untrusted certificate bundles.

Graph production and LP search run sequentially in small chunks. Completed
machines have append-only records; only an interrupted final line may be
truncated. check_weighted_v2.py performs kernel replay and census discharge.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

from check_weighted import source_hashes as proof_sources
from generate_pipeline_examples import codes
from weighted_codec_v2 import pack, bundle_encode
from weighted_search_v2 import BudgetExpired, solve_graph, install_budget, budget

ROOT=Path(__file__).resolve().parents[1]


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    temp=path.with_suffix(path.suffix+'.tmp')
    temp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');temp.replace(path)


def recover(path):
    rows=[];offset=0
    if not path.exists():return rows
    with path.open('rb') as stream:
        while line:=stream.readline():
            try:row=json.loads(line)
            except (json.JSONDecodeError,UnicodeDecodeError):
                if line.endswith(b'\n') or stream.read(1):raise ValueError('Corrupt committed ledger')
                with path.open('r+b') as output:output.truncate(offset)
                break
            if not line.endswith(b'\n'):
                with path.open('ab') as output:output.write(b'\n')
            rows.append(row);offset+=len(line)
            if not line.endswith(b'\n'):break
    if len({r['machine'] for r in rows})!=len(rows):raise ValueError('Duplicate ledger entry')
    return rows


def emit_bundles(rows,directory,registry,source):
    directory.mkdir(parents=True,exist_ok=True)
    candidates=[row['candidate'] for row in rows if row['candidate'] is not None]
    shards=[];batch=[];size=0;limit=4*1024*1024
    def flush():
        if not batch:return
        path=directory/f'certificates-{len(shards):04d}.json'
        content=bundle_encode(batch);temporary=path.with_suffix('.json.tmp')
        temporary.write_text(content);temporary.replace(path)
        if path.stat().st_size>limit:raise ValueError('Encoded shard exceeds 4MiB')
        shards.append({'path':str(path.resolve().relative_to(ROOT)),'rows':len(batch),
                       'bytes':len(content.encode()),'sha256':sha(path)})
    for row in candidates:
        length=len((json.dumps(row,separators=(',',':'))+'\n').encode())
        if length>limit:raise ValueError('Oversize certificate retained in ledger: '+row['machine'])
        if batch and (len(batch)>=512 or size+length>limit):flush();batch=[];size=0
        batch.append(row);size+=length
    flush()
    data={'format':'BBB24 compact weighted certificates v2',
          'status':'Untrusted candidates; kernel replay and census discharge required.',
          'source':source,'rows':len(candidates),'kinds':dict(Counter(row['kind'] for row in candidates)),
          'bundles':shards}
    atomic_json(registry,data)
    return data


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--bundle-dir',type=Path,required=True)
    parser.add_argument('--registry',type=Path,required=True)
    parser.add_argument('--binary',type=Path,default=ROOT/'build/weighted-v2/dump')
    parser.add_argument('--width',type=int,default=2)
    parser.add_argument('--anchor',type=int,default=256)
    parser.add_argument('--fuel',type=int,default=8193)
    parser.add_argument('--rounds',type=int,default=33)
    parser.add_argument('--graph-timeout',type=float,default=0.2)
    parser.add_argument('--node-limit',type=int,default=2048)
    parser.add_argument('--wall-width',type=int,default=16)
    parser.add_argument('--lp-timeout',type=float,default=1)
    parser.add_argument('--chunk-size',type=int,default=32)
    parser.add_argument('--check',action='store_true',help='Validate frozen run hashes only')
    args=parser.parse_args()
    if not (1<=args.width<=8 and 0<=args.anchor<=4096 and args.fuel>0 and args.rounds>0 and
            args.node_limit>0 and args.wall_width>=0 and 1<=args.chunk_size<=128 and
            0<args.graph_timeout<float('inf') and 0<args.lp_timeout<float('inf')):parser.error('Invalid budgets')
    machines=args.input.read_text().splitlines()
    if not machines or len(set(machines))!=len(machines):raise ValueError('Empty/duplicate input')
    for machine in machines:codes(machine)
    params={k:getattr(args,k) for k in ('width','anchor','fuel','rounds','graph_timeout','node_limit','wall_width','lp_timeout','chunk_size')}
    sources=proof_sources()
    for filename in ('ExtractWeightedV2.v','weighted_graphs_v2.ml','weighted_search_v2.py',
                     'weighted_campaign_v2.py','weighted_codec_v2.py','weighted_search.py',
                     'generate_pipeline_examples.py'):
        sources['tools/'+filename]=sha(ROOT/'tools'/filename)
    sources['../tools/multisymbol/weighted_certificates.py']=sha(ROOT.parent/'tools/multisymbol/weighted_certificates.py')
    import scipy
    manifest={'input_sha256':sha(args.input),'input_rows':len(machines),'source_sha256':sources,
              'binary_sha256':sha(args.binary),'parameters':params,'scipy_version':scipy.__version__}
    args.output_dir.mkdir(parents=True,exist_ok=True)
    manifest_path=args.output_dir/'manifest.json'
    if manifest_path.exists() and json.loads(manifest_path.read_text())!=manifest:raise ValueError('Frozen inputs/sources differ; use a fresh directory')
    if args.check:
        report=json.loads((args.output_dir/'summary.json').read_text())
        if report['manifest_sha256']!=sha(manifest_path) or report['results_sha256']!=sha(args.output_dir/'results.jsonl') or report['registry_sha256']!=sha(args.registry):raise ValueError('Saved artifact differs')
        for bundle in json.loads(args.registry.read_text())['bundles']:
            if sha(ROOT/bundle['path'])!=bundle['sha256']:raise ValueError('Saved bundle differs')
        print('Validated frozen search registry; no proof claim.');return
    atomic_json(manifest_path,manifest)
    ledger=args.output_dir/'results.jsonl';results=recover(ledger)
    if [r['machine'] for r in results]!=machines[:len(results)]:raise ValueError('Result ledger is not an input prefix')
    pending=machines[len(results):]
    install_budget()
    started=time.monotonic()
    with ledger.open('a') as output:
        for offset in range(0,len(pending),args.chunk_size):
            batch=pending[offset:offset+args.chunk_size]
            chunk=args.output_dir/'chunk-input.txt';chunk.write_text(''.join(m+'\n' for m in batch))
            graph_path=args.output_dir/'chunk-graphs.jsonl'
            command=[str(args.binary.resolve()),str(chunk.resolve()),str(args.width),str(args.anchor),str(args.fuel),str(args.rounds),str(args.graph_timeout),str(args.node_limit)]
            with graph_path.open('w') as stream:
                subprocess.run(command,stdout=stream,stderr=subprocess.PIPE,check=True,
                               timeout=max(30,(2*args.graph_timeout+1)*len(batch)))
            events=[json.loads(line) for line in graph_path.read_text().splitlines()]
            if [(e['machine'],e['mirror']) for e in events]!=[(m,r) for m in batch for r in (0,1)]:raise ValueError('Graph inventory mismatch')
            for index,machine in enumerate(batch):
                pair=events[2*index:2*index+2];candidate=None;diagnostics=Counter();begin=time.monotonic()
                for event in pair:
                    if event['status']=='ordinary_candidate':
                        candidate={'kind':'ordinary','machine':machine,'mirror':event['mirror'],'n':args.width,
                                   't':args.anchor,'fuel':args.fuel,'rounds':args.rounds};break
                if candidate is None:
                    for event in pair:
                        graph=event.get('graph')
                        if not graph:continue
                        try:
                            with budget(args.lp_timeout):row=solve_graph(graph,args.wall_width,diagnostics)
                            if row is not None:candidate=pack(row);break
                        except BudgetExpired:diagnostics['lp_timeout']+=1
                result={'machine':machine,'orientations':[{k:v for k,v in e.items() if k!='graph'} for e in pair],
                        'candidate':candidate,'diagnostics':dict(diagnostics),'lp_seconds':round(time.monotonic()-begin,6)}
                output.write(json.dumps(result,separators=(',',':'))+'\n');output.flush();os.fsync(output.fileno())
                results.append(result)
            print(json.dumps({'completed':len(results),'input_rows':len(machines),
                              'candidates':sum(r['candidate'] is not None for r in results),
                              'seconds_this_process':round(time.monotonic()-started,2)},sort_keys=True),flush=True)
    if manifest['input_sha256']!=sha(args.input) or manifest['binary_sha256']!=sha(args.binary):raise ValueError('Inputs changed during campaign')
    for relative,digest in sources.items():
        if sha(ROOT/relative)!=digest:raise ValueError('Source changed during campaign: '+relative)
    registry=emit_bundles(results,args.bundle_dir,args.registry,
                          {'manifest_sha256':sha(manifest_path),'results_sha256':sha(ledger),'input_sha256':sha(args.input),'input_rows':len(machines)})
    orientations=[event for row in results for event in row['orientations']]
    summary={'status':'Complete exploratory search; no checked or discharged claim.','input_rows':len(machines),
             'candidate_rows':registry['rows'],'kinds':registry['kinds'],
             'orientation_statuses':dict(Counter(e['status'] for e in orientations)),
             'graph_seconds':round(sum(e['seconds'] for e in orientations),3),
             'lp_seconds':round(sum(r['lp_seconds'] for r in results),3),
             'manifest_sha256':sha(manifest_path),'results_sha256':sha(ledger),'registry_sha256':sha(args.registry)}
    atomic_json(args.output_dir/'summary.json',summary)
    print(json.dumps(summary,sort_keys=True),flush=True)


if __name__=='__main__':main()
