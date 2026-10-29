"""Replay exact frozen S011 with its unary-return invariant and state-zero census wrapper.

Universal iteration, drain, and terminal macros prove positive blank-entry returns.
The eleven boundary and exact-transition regressions are recursively audited.
"""
import argparse,hashlib,json,resource,subprocess,time
from pathlib import Path
from check_campaign import dependency_hashes,inventory_source
from generate_pipeline_examples import codes
import check_burn9_context_marker as wrappers
import kernel_audit_cache_v3 as kernel

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn20-unary-counter/proof'
NS='BBB24Burn20UnaryCounter'
PREFIX=ROOT/'research/burn20-unary-counter'
MACHINE='1LB0LB2RA2LA_2RB2RA3LB1RB'
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
From {NS} Require Import UnaryCounter Regression.
Import ListNotations.
Definition machine_0 := uc_tm.
Lemma exact_complete_table : forall q s,machine_0 q s=machine_of_codes[{table}]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Theorem nonhalt_0 : NonHalt machine_0.
Proof. exact uc_nonhalt. Qed.
Theorem state_zero_0 : QHBound 0 machine_0.
Proof. exact uc_state_zero. Qed.
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
    assert data['metadata_revision']==1
    checkpoint=ROOT/'research/state-holdouts-78.txt'
    assert sha(checkpoint)==data['frozen_checkpoint_sha256']
    assert MACHINE in checkpoint.read_text().splitlines()
    assert codes(MACHINE)==[5,1,10,8,11,10,13,7]
    assert rows[0]['code']==sum(v*17**i for i,v in enumerate(codes(MACHINE)))
    selection=ROOT/data['selection_report'];assert sha(selection)==data['selection_sha256']
    selection_data=json.loads(selection.read_text())
    assert rows==selection_data['rows'] and selection_data['metadata_revision']==1
    assert selection_data['main_cost']==dict(quadratic=8,linear=12,constant=7)
    assert selection_data['drain_cost']==dict(k_squared=2,m_times_k=4,k_linear=5)
    templates=[ROOT/'proof-sources/burn20-unary-counter'/name for name in ('UnaryCounter.v','Regression.v')]
    template_pins={str(p.relative_to(ROOT)):sha(p)for p in templates};assert template_pins==data['template_sha256']
    load_paths=[(ROOT/'theories','BBB24'),(BUILD,NS)];flags=[x for p,ns in load_paths for x in ('-Q',str(p),ns)]
    files=[]
    for p in templates:
        out=BUILD/p.name;exact(out,p.read_text());files.append(out)
    p=BUILD/'Example00.v';exact(p,example(0,rows[0]));files.append(p)
    p=BUILD/'Board.v';exact(p,board(rows));files.append(p)
    descriptor=dict(id='burn20_unary_counter',scope='state',rows=1,state_bound=0,instruction_bound=None,
                    module=NS+'.Inventory',board='board',small_sound='small_sound',sound='sound',was_pending='was_pending',
                    proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)),exact_inventory_theorem=NS+'.Inventory.inventory_exact',
                    inventories=[dict(path=str(invpath.relative_to(ROOT)),format='rows')],
                    load_paths=[dict(path=str(BUILD.relative_to(ROOT)),namespace=NS)])
    p=BUILD/'Inventory.v';exact(p,inventory_source(dict(descriptor,module=NS+'.Board',machines=[MACHINE])));files.append(p)
    sources=dependency_hashes(files,flags)
    for name in ('check_burn20_unary_counter.py','check_burn20_unary_counter_native.py','check_burn9_context_marker.py','check_campaign.py','check_shadow_links.py',
                 'generate_pipeline_examples.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name]=sha(ROOT/'tools'/name)
    inputs={str(p.relative_to(ROOT)):sha(p)for p in (inp,selection,checkpoint)}
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
    current=dict(stable,scope='Exact complete unary-counter state-zero family, every completion; no instruction claim.',
                 compile_seconds=timings,kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),
                 kernel_audit='Full recursive coqchk including regressions.',audit_seconds=round(time.monotonic()-begin,3),
                 checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
                 object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo'))for p in files})
    if old is None:exact(invpath,inventory);exact(report,json.dumps(current,indent=2,sort_keys=True)+'\n')
    (BUILD/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n')
    print('Complete unary-counter state family fully audited.',flush=True)

if __name__=='__main__':main()
