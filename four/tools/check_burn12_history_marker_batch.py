"""Replay a separate exact exact batch with the frozen historical marker theorem.

The four-family historical-marker pilot remains immutable. This runner imports its
proved theorem and renderer, rechecks every compact machine/parameter tuple in
Coq, and audits the complete new inventory dependency closure without reuse.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
from generate_pipeline_examples import codes
import kernel_audit_cache_v3 as kernel
import check_burn12_history_marker as pilot

ROOT=Path(__file__).resolve().parents[1]


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path,text):
    if path.exists() and path.read_text()!=text:raise ValueError('Frozen artifact differs: '+str(path))
    if not path.exists():path.write_text(text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch',default='partial13')
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--audit-timeout',type=int,default=5400)
    args=parser.parse_args()
    if not re.fullmatch('[a-z][a-z0-9]*',args.batch) or min(args.timeout,args.audit_timeout)<=0:
        parser.error('Simple lowercase batch identifier and positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    prefix='burn12-history-marker-'+args.batch
    output=ROOT/'build'/prefix/'proof';output.mkdir(parents=True,exist_ok=True)
    namespace='BBB24Burn12HistoryMarker'+args.batch.capitalize()
    input_path=ROOT/'research'/(prefix+'-proof-input.json')
    report_path=ROOT/'research'/(prefix+'-checked.json')
    inventory_path=ROOT/'research'/(prefix+'-machines.json')
    old=json.loads(report_path.read_text()) if report_path.exists() else None
    protected={p:sha(p) for p in (report_path,inventory_path) if p.exists()}
    data=json.loads(input_path.read_text());rows=data['rows']
    assert 0<len(rows)<=493 and len({r['machine'] for r in rows})==len(rows) and data['state_bound']==0
    selection=ROOT/data['selection_report'];assert sha(selection)==data['selection_sha256']
    assert rows==json.loads(selection.read_text())['rows']
    for row in rows:
        assert row['code']==sum(v*17**i for i,v in enumerate(codes(row['machine'])))
        assert len(row['weights'])==4 and row['weights'][0]==0
        assert row['invariant']=='conditional' and 0<row['history_marker_mask']<256
    dependency_report=ROOT/'research/burn12-history-marker-checked.json'
    assert sha(dependency_report)==data['generic_report_sha256']
    generic=json.loads(dependency_report.read_text())
    for group in ('inputs_sha256','template_sha256','source_sha256','object_sha256'):
        for name,digest in generic[group].items():assert sha(ROOT/name)==digest,name
    load_paths=[(ROOT/'theories','BBB24'),(pilot.OUTPUT,pilot.NS),(output,namespace)]
    flags=[part for p,ns in load_paths for part in ('-Q',str(p),ns)]
    files=[]
    for i,row in enumerate(rows):
        path=output/f'Example{i:02d}.v';exact(path,pilot.example(i,row));files.append(path)
    source=pilot.board(rows).replace('From '+pilot.NS+' Require Import Example',
                                    'From '+namespace+' Require Import Example')
    path=output/'Board.v';exact(path,source);files.append(path)
    descriptor=dict(id='burn12_history_marker_'+args.batch,scope='state',rows=len(rows),state_bound=0,
                    instruction_bound=None,module=namespace+'.Inventory',board='board',small_sound='small_sound',
                    sound='sound',was_pending='was_pending',proof_source=str((output/'Inventory.v').relative_to(ROOT)),
                    exact_inventory_theorem=namespace+'.Inventory.inventory_exact',
                    inventories=[dict(path=str(inventory_path.relative_to(ROOT)),format='rows')],
                    load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=ns) for p,ns in load_paths[1:]])
    path=output/'Inventory.v';exact(path,inventory_source(dict(descriptor,module=namespace+'.Board',machines=[r['machine'] for r in rows])));files.append(path)
    sources=dependency_hashes(files,flags)
    for name in ('check_burn12_history_marker_batch.py','check_burn12_history_marker.py','check_burn9_context_marker.py','check_campaign.py',
                 'check_shadow_links.py','generate_pipeline_examples.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name]=sha(ROOT/'tools'/name)
    inputs={str(p.relative_to(ROOT)):sha(p) for p in (input_path,selection,dependency_report)}
    inventory=json.dumps(dict(rows=[dict(machine=r['machine']) for r in rows]),indent=2)+'\n'
    stable=dict(inputs_sha256=inputs,source_sha256=sources,descriptor=descriptor,
                inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
                checked_state_families=len(rows),checked_instruction_families=0)
    if old:assert all(old[k]==v for k,v in stable.items())
    timings={}
    for path in files:
        started=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        timings[path.stem]=round(time.monotonic()-started,3)
        print('Compiled '+path.stem+': '+str(timings[path.stem])+'s',flush=True)
    receipt,log=kernel.fresh_paths(output,'kernel-audit');started=time.monotonic()
    audit=kernel.audit([namespace+'.Inventory'],[files[-1]],load_paths,receipt,log,recursive=True,timeout=args.audit_timeout)
    assert all(sha(ROOT/p)==h for p,h in {**inputs,**sources}.items())
    assert all(sha(p)==h for p,h in protected.items())
    current=dict(stable,scope='Exact historical-marker state-zero census families, all completions. No instruction claim.',
                 compile_seconds=timings,kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),
                 kernel_audit='Full recursive coqchk.',audit_seconds=round(time.monotonic()-started,3),
                 checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
                 object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in files})
    if old is None:
        exact(inventory_path,inventory);exact(report_path,json.dumps(current,indent=2,sort_keys=True)+'\n')
    (output/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n')
    print(str(len(rows))+' historical-marker state families fully audited.',flush=True)


if __name__=='__main__':main()
