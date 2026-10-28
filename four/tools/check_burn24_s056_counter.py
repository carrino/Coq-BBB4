"""Replay S056 three-phase counter normalization and its exact state-zero family.

Universal three-phase macros and all-token fallback prove the closed
nonzero reset residues. The frozen burn18 local carry is imported unchanged.
Native controls provide provenance. All sixteen regressions are audited.
"""
import argparse,hashlib,json,resource,subprocess,time
from pathlib import Path
from check_campaign import dependency_hashes,inventory_source
from generate_pipeline_examples import codes
import check_burn9_context_marker as wrappers
import kernel_audit_cache_v3 as kernel

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn24-s056-counter/proof'
NS='BBB24Burn24S056Counter'
PREFIX=ROOT/'research/burn24-s056-counter'
MACHINE='1LB2LB1RA3RA_3RB3LA2RB2LB'
def artifact(s):return PREFIX.with_name(PREFIX.name+'-'+s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def exact(p,s):
    if p.exists()and p.read_text()!=s:raise ValueError('Frozen artifact differs: '+str(p))
    if not p.exists():p.write_text(s)

def example(i,row):
    assert i==0 and row['machine']==MACHINE
    table=';'.join(map(str,codes(row['machine'])))
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline.
From BBB24Burn18CounterObligations Require Import CounterObligations.
From {NS} Require Import Phase Fallback Return Regression.
Import ListNotations.
Definition machine_0 := s56_tm.
Lemma exact_complete_table : forall q s,machine_0 q s=machine_of_codes[{table}]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Theorem nonhalt_0 : NonHalt machine_0.
Proof. exact(proj1 sf_sound). Qed.
Theorem state_zero_0 : QHBound 0 machine_0.
Proof. exact(proj2 sf_sound). Qed.
Print Assumptions state_zero_0.
'''

def board(rows):
    return wrappers.board(rows).replace('From '+wrappers.NS+' Require Import Example','From '+NS+' Require Import Example')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout',type=int,default=600);parser.add_argument('--audit-timeout',type=int,default=3600)
    args=parser.parse_args()
    if min(args.timeout,args.audit_timeout)<=0:parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));BUILD.mkdir(parents=True,exist_ok=True)
    inp=artifact('proof-input.json');report=artifact('checked.json');invpath=artifact('machines.json')
    old=json.loads(report.read_text())if report.exists()else None
    protected={p:sha(p)for p in(report,invpath)if p.exists()}
    data=json.loads(inp.read_text());rows=data['rows']
    assert len(rows)==1 and rows[0]['machine']==MACHINE and data['state_bound']==0
    assert rows[0]['code']==sum(v*17**i for i,v in enumerate(codes(MACHINE)))
    selection=ROOT/data['selection_report'];assert sha(selection)==data['selection_sha256']
    assert rows==json.loads(selection.read_text())['rows']
    templates=[ROOT/'proof-sources/burn24-s056-counter'/name for name in ('Phase.v','Fallback.v','Return.v','Regression.v')]
    template_pins={str(p.relative_to(ROOT)):sha(p)for p in templates};assert template_pins==data['template_sha256']
    load_paths=[(ROOT/'theories','BBB24'),(ROOT/'build/burn18-counter-obligations/proof','BBB24Burn18CounterObligations'),(BUILD,NS)];flags=[x for p,ns in load_paths for x in ('-Q',str(p),ns)]
    files=[]
    for p in templates:
        out=BUILD/p.name;exact(out,p.read_text());files.append(out)
    p=BUILD/'Example00.v';exact(p,example(0,rows[0]));files.append(p)
    p=BUILD/'Board.v';exact(p,board(rows));files.append(p)
    descriptor=dict(id='burn24_s056_counter',scope='state',rows=1,state_bound=0,instruction_bound=None,
                    module=NS+'.Inventory',board='board',small_sound='small_sound',sound='sound',was_pending='was_pending',
                    proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)),exact_inventory_theorem=NS+'.Inventory.inventory_exact',
                    inventories=[dict(path=str(invpath.relative_to(ROOT)),format='rows')],
                    load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=ns)for p,ns in load_paths if ns!='BBB24'])
    p=BUILD/'Inventory.v';exact(p,inventory_source(dict(descriptor,module=NS+'.Board',machines=[MACHINE])));files.append(p)
    sources=dependency_hashes(files,flags)
    for name in ('check_burn24_s056_counter.py','check_burn9_context_marker.py','check_campaign.py','check_shadow_links.py',
                 'generate_pipeline_examples.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name]=sha(ROOT/'tools'/name)
    inherited=ROOT/'proof-sources/burn18-counter-obligations/CounterObligations.v'
    assert sha(inherited)==sha(ROOT/'build/burn18-counter-obligations/proof/CounterObligations.v')
    sources[str(inherited.relative_to(ROOT))]=sha(inherited)
    inputs={str(p.relative_to(ROOT)):sha(p)for p in (inp,selection,ROOT/'research/burn18-counter-obligations-checked.json')}
    inventory=json.dumps(dict(rows=[dict(machine=MACHINE)]),indent=2)+'\n'
    stable=dict(inputs_sha256=inputs,template_sha256=template_pins,source_sha256=sources,descriptor=descriptor,
                inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),checked_state_families=1,checked_instruction_families=0)
    if old:assert all(old[k]==v for k,v in stable.items())
    timings={}
    for p in files:
        begin=time.monotonic()
        with p.with_suffix('.log').open('w')as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(p)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        timings[p.stem]=round(time.monotonic()-begin,3);print('Compiled '+p.stem+': '+str(timings[p.stem])+'s',flush=True)
    receipt,log=kernel.fresh_paths(BUILD,'kernel-audit');begin=time.monotonic()
    audit=kernel.audit([NS+'.Inventory'],[files[-1]],load_paths,receipt,log,recursive=True,timeout=args.audit_timeout)
    assert NS+'.Regression'in audit['checked_modules']
    assert all(sha(ROOT/p)==h for p,h in {**inputs,**sources,**template_pins}.items())
    assert all(sha(p)==h for p,h in protected.items())
    current=dict(stable,scope='Exact complete S056 three-phase counter state-zero family, every completion; no instruction claim.',
                 compile_seconds=timings,kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),
                 kernel_audit='Full recursive coqchk including regressions.',audit_seconds=round(time.monotonic()-begin,3),
                 checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
                 object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo'))for p in files})
    if old is None:exact(invpath,inventory);exact(report,json.dumps(current,indent=2,sort_keys=True)+'\n')
    (BUILD/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n')
    print('Complete S056 three-phase counter state family fully audited.',flush=True)

if __name__=='__main__':main()
