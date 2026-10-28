"""Reproduce frozen legacy/V2 weighted proofs without rewriting their reports.

Portable evidence consists of the exact generated Coq sources, compiled objects,
manifest, and machine inventory. V2 timed .receipt.json files are historical
local cache metadata: their elapsed seconds cannot be regenerated portably and
are explicitly excluded here. All proof artifacts are byte-checked and audited.
"""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import re
import subprocess
import time

import check_weighted as legacy
import check_weighted_v2 as v2
from weighted_codec_v2 import bundle_decode
from weighted_render import render

ROOT=Path(__file__).resolve().parents[1]


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def serialized(value):return json.dumps(value,indent=2,sort_keys=True)+'\n'


def write_exact(path,text,expected):
    if hashlib.sha256(text.encode()).hexdigest()!=expected:
        raise ValueError('Regenerated source bytes differ from frozen report: '+path.name)
    if path.exists() and sha(path)!=expected:
        raise ValueError('Existing artifact differs; use a fresh output directory: '+str(path))
    if not path.exists():path.write_text(text)


def run(command,log,timeout):
    with log.open('w') as output:
        subprocess.run(command,cwd=ROOT.parent,stdout=output,stderr=subprocess.STDOUT,
                       check=True,timeout=timeout)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    data=parser.add_mutually_exclusive_group(required=True)
    data.add_argument('--certificates',type=Path,help='Legacy JSONL certificate input')
    data.add_argument('--registry',type=Path,help='V2 compact-bundle registry')
    parser.add_argument('--inventory',type=Path,help='Override V2 tracked inventory location')
    parser.add_argument('--timeout',type=int,default=1800)
    args=parser.parse_args()
    if args.timeout<1:parser.error('Positive timeout required')
    report_hash=sha(args.report);report=json.loads(args.report.read_text());manifest=report['manifest']
    namespace=manifest['namespace']
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*',namespace):raise ValueError('Invalid recorded namespace')
    if manifest['state_bound']!=4096 or manifest['instruction_bound']!=4096:raise ValueError('Unexpected recorded bound')
    version=subprocess.run(['coqc','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0]
    if version!=manifest['coq_version']:raise ValueError('Coq version differs from the frozen report')
    args.output_dir.mkdir(parents=True,exist_ok=True)
    flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(args.output_dir.resolve()),namespace]
    texts={'manifest.json':serialized(manifest)}
    checked=[row for row in report['results'] if row['status']=='coq_checked']
    checked_names=[row['machine'] for row in checked]
    if len(set(checked_names))!=len(checked_names):raise ValueError('Repeated checked machine')
    recorded=report['artifacts_sha256']
    historical=[];inventory=None
    if args.certificates is not None:
        if 'certificates_sha256' not in manifest or sha(args.certificates)!=manifest['certificates_sha256']:
            raise ValueError('Legacy certificate input differs')
        if legacy.source_hashes()!=manifest['source_sha256']:raise ValueError('Frozen legacy sources differ')
        rows=[json.loads(line) for line in args.certificates.read_text().splitlines()]
        if len(rows)!=manifest['rows']:raise ValueError('Legacy input count differs')
        for index,row in enumerate(rows):texts[f'Weighted{index:04d}.v']=render(row)
        modules=[]
        for result in checked:
            name=result['module']
            if not re.fullmatch(r'Weighted\d{4}',name):raise ValueError('Invalid legacy module')
            index=int(name[8:])
            if rows[index]['graph']['machine']!=result['machine']:raise ValueError('Legacy row mapping differs')
            modules.append(name)
        texts['WeightedBoard.v']=legacy.board_source(namespace,modules)
        texts['machines.txt']=''.join(machine+'\n' for machine in checked_names)
        aggregate='WeightedBoard'
        source_snapshot=lambda:legacy.source_hashes()
        expected_sources=manifest['source_sha256']
    else:
        if 'registry_sha256' not in manifest or sha(args.registry)!=manifest['registry_sha256']:
            raise ValueError('V2 bundle registry differs')
        for version_number in (4,3):
            if f'tools/check_weighted_v{version_number}.py' in manifest['sources_sha256']:
                importlib.import_module(f'check_weighted_v{version_number}').configure()
                break
        if v2.sources(flags)!=manifest['sources_sha256']:raise ValueError('Frozen V2 sources differ')
        registry=json.loads(args.registry.read_text());rows=[]
        for bundle in registry['bundles']:
            path=ROOT/bundle['path']
            if sha(path)!=bundle['sha256']:raise ValueError('V2 bundle differs: '+bundle['path'])
            part=bundle_decode(path.read_text())
            if len(part)!=bundle['rows']:raise ValueError('V2 bundle count differs')
            rows+=part
        if len(rows)!=manifest['rows'] or len(rows)!=registry['rows'] or len({r['machine'] for r in rows})!=len(rows):
            raise ValueError('V2 input inventory differs')
        by_machine={row['machine']:row for row in rows}
        if [r['machine'] for r in report['results']]!=[r['machine'] for r in rows]:raise ValueError('V2 recorded result order differs')
        grouped={}
        for result in checked:
            name=result['module']
            if not re.fullmatch(r'Weighted\d{5}[AB]*',name):raise ValueError('Invalid V2 shard name')
            grouped.setdefault(name,[]).append(by_machine[result['machine']])
        modules=list(grouped)
        for name,batch in grouped.items():texts[name+'.v']=v2.shard_source(batch)
        texts['WeightedAll.v']=v2.aggregate(namespace,modules)
        aggregate='WeightedAll'
        historical=[name for name in recorded if name.endswith('.receipt.json')]
        if set(historical)!={name+'.receipt.json' for name in modules}:raise ValueError('Unexpected historical cache inventory')
        machine_inputs=report['descriptor']['machine_inputs']
        if len(machine_inputs)!=1 or machine_inputs[0]['format']!='json_rows':raise ValueError('Unexpected V2 inventory descriptor')
        inventory=args.inventory or ROOT/machine_inputs[0]['path']
        expected_inventory=serialized({'rows':[{'machine':machine} for machine in checked_names]})
        if hashlib.sha256(expected_inventory.encode()).hexdigest()!=report['inventory_sha256'] or sha(inventory)!=report['inventory_sha256']:
            raise ValueError('V2 exact inventory differs')
        source_snapshot=lambda:v2.sources(flags)
        expected_sources=manifest['sources_sha256']
    objects={name+'.vo' for name in [*modules,aggregate]}
    portable={name:digest for name,digest in recorded.items() if name not in historical}
    if set(portable)!=set(texts)|objects:raise ValueError('Unrecognized portable artifact inventory')
    for name,text in texts.items():write_exact(args.output_dir/name,text,portable[name])
    started=time.monotonic()
    for index,name in enumerate([*modules,aggregate]):
        path=args.output_dir/(name+'.v');vo=path.with_suffix('.vo')
        if vo.exists():
            if sha(vo)!=portable[vo.name]:raise ValueError('Existing compiled artifact differs; use a fresh output directory: '+vo.name)
        else:
            run(['coqc','-noglob','-native-compiler','no',*flags,str(path.resolve())],path.with_suffix('.replay.log'),args.timeout)
            if sha(vo)!=portable[vo.name]:raise ValueError('Recompiled object bytes differ: '+vo.name)
        if (index+1)%25==0 or name==aggregate:
            print(f'Reconstructed {index+1}/{len(modules)+1} exact recorded objects.',flush=True)
    run(['coqchk','-silent','-bytecode-compiler','yes',*flags,namespace+'.'+aggregate,'BBB24.WeightedRegression'],
        args.output_dir/'recorded-coqchk.log',args.timeout*max(1,len(modules)))
    for name,digest in portable.items():
        if sha(args.output_dir/name)!=digest:raise ValueError('Artifact changed during audit: '+name)
    if source_snapshot()!=expected_sources or sha(args.report)!=report_hash:raise ValueError('Frozen report or sources changed during replay')
    if inventory is not None and sha(inventory)!=report['inventory_sha256']:raise ValueError('Inventory changed during replay')
    if args.registry is not None:
        if sha(args.registry)!=manifest['registry_sha256']:raise ValueError('Registry changed during replay')
        for bundle in registry['bundles']:
            if sha(ROOT/bundle['path'])!=bundle['sha256']:raise ValueError('Bundle changed during replay')
    if args.certificates is not None:
        if sha(args.certificates)!=manifest['certificates_sha256']:raise ValueError('Legacy certificates changed during replay')
        run(['python3',str(ROOT/'tools/check_weighted.py'),'--certificates',str(args.certificates.resolve()),
             '--output-dir',str(args.output_dir.resolve()),'--report',str(args.report.resolve()),'--namespace',namespace,'--check'],
            args.output_dir/'legacy-check.log',args.timeout)
    receipt={'status':'Exact recorded proof artifacts reconstructed and recursively kernel audited.',
             'frozen_report_sha256':report_hash,'wrapper_sha256':sha(Path(__file__)),
             'portable_artifacts_sha256':portable,'historical_timed_cache_artifacts':historical,
             'checked_families':len(checked),'seconds':round(time.monotonic()-started,3)}
    (args.output_dir/'recorded-replay.json').write_text(serialized(receipt))
    print(f'Replayed {len(checked)} checked families; frozen report unchanged; {len(historical)} historical timed receipts excluded.',flush=True)


if __name__=='__main__':main()
