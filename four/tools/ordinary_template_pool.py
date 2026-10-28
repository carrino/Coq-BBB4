"""Expose ordinary n-gram contexts as untrusted reusable-tail source data.

The exporter does no ranking search and claims no bounds. Its closed contexts
use empty explicit weighted certificates, so every replay recomputes ordinary
rankings in the existing Coq checker. Source and target proof counts are never
inferred from this graph-only search.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import time

from kernel_audit_cache import digest
from weighted_codec_v2 import bundle_decode,bundle_encode,unpack

ROOT=Path(__file__).resolve().parents[1]


def write_frozen(path,text):
    if path.exists() and path.read_text()!=text:raise ValueError('Frozen output changed: '+str(path))
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--build',type=Path,default=ROOT/'build/ordinary-templates/full')
    parser.add_argument('--timeout',type=float,default=1.)
    parser.add_argument('--limit',type=int,default=0)
    parser.add_argument('--max-nodes',type=int,default=2048)
    args=parser.parse_args()
    if not 0<args.timeout<=60 or args.limit<0 or args.max_nodes<1:raise ValueError('Invalid budget')
    registry=json.loads(args.registry.read_text());source=[]
    pins={str(args.registry.resolve().relative_to(ROOT)):digest(args.registry)}
    for e in registry['bundles']:
        path=ROOT/e['path']
        if digest(path)!=e['sha256']:raise ValueError('Source bundle changed')
        rows=bundle_decode(path.read_text())
        if len(rows)!=e['rows']:raise ValueError('Source row count changed')
        source.extend(r for r in rows if r['kind']=='ordinary');pins[e['path']]=digest(path)
    if args.limit:source=source[:args.limit]
    if not source:raise ValueError('No ordinary sources')
    build=args.build.resolve();build.mkdir(parents=True,exist_ok=True)
    input_path=build/'input.tsv';input_path.write_text(''.join('\t'.join(str(r[k])for k in ['machine','mirror','n','t','fuel','rounds'])+'\n'for r in source))
    extracted=ROOT/'build/weighted-v2/weighted_v2.cmx';producer=ROOT/'tools/ordinary_template_graphs.ml';binary=build/'dump';obj=build/'ordinary_template_graphs.cmx'
    for p in [Path(__file__),producer,extracted,extracted.with_suffix('.o'),extracted.with_suffix('.cmi'),extracted.with_suffix('.ml'),extracted.with_suffix('.mli')]:
        pins[str(p.resolve().relative_to(ROOT))]=digest(p)
    subprocess.run(['ocamlopt','-I',str(extracted.parent),'-c','-o',str(obj),str(producer)],check=True)
    subprocess.run(['ocamlopt','-I',str(extracted.parent),'-o',str(binary),'unix.cmxa',str(extracted),str(obj)],check=True)
    start=time.monotonic();events_path=build/'events.jsonl'
    with events_path.open('w')as f:subprocess.run([str(binary),str(input_path),str(args.timeout)],stdout=f,check=True)
    events=[json.loads(l)for l in events_path.read_text().splitlines()]
    if len(events)!=len(source):raise ValueError('Exporter omitted a row')
    pool=[];counts=Counter()
    for src,event in zip(source,events):
        if src['machine']!=event['machine']:raise ValueError('Exporter reordered rows')
        counts[event['status']]+=1
        if event['status']!='closed':continue
        if len(event['nodes'])>args.max_nodes:counts['node_limit']+=1;continue
        row={**src,'kind':'weighted','nodes':event['nodes'],'certs':{},'components':[]}
        unpack(row);pool.append(row)
    if not pool:raise ValueError('No closed templates; no registry emitted')
    directory=args.output.resolve().parent;bundles=[]
    for offset in range(0,len(pool),128):
        rows=pool[offset:offset+128];path=directory/f'contexts-{offset//128:04}.json'
        text=bundle_encode(rows);write_frozen(path,text)
        bundles.append(dict(path=str(path.relative_to(ROOT)),sha256=digest(path),rows=len(rows),bytes=path.stat().st_size))
    result=dict(format='BBB24 compact weighted certificates v2',rows=len(pool),kinds=dict(weighted=len(pool)),bundles=bundles,
                source=dict(inputs_sha256=pins,ordinary_inputs=len(source),event_sha256=digest(events_path),binary_sha256=digest(binary),
                            timeout_seconds=args.timeout,max_nodes=args.max_nodes,status_counts=dict(counts)),
                status='Untrusted ordinary closure templates, with empty explicit certificates; all rankings and target boots require Coq replay.')
    if any(digest(ROOT/p)!=h for p,h in pins.items()):raise ValueError('Source changed during extraction')
    write_frozen(args.output,json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(ordinary_inputs=len(source),templates=len(pool),status_counts=dict(counts),seconds=time.monotonic()-start)))


if __name__=='__main__':main()
