"""Replay both-state contextual-marker state proofs in an isolated namespace.

Closed history graphs prove actual nonhalting. A new theorem preserves
the right marker in both states; frozen capacity and conditional B recurrence
permits unreachable undefined A cells. No instruction bound is claimed.
"""
import argparse,hashlib,json
from pathlib import Path
import resource,subprocess,time
from check_campaign import dependency_hashes,inventory_source
from generate_pipeline_examples import codes
import kernel_audit_cache_v3 as kernel
import check_burn9_context_marker as original
import check_burn10_marker_history as partial
ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn11-global-marker/proof'
NS='BBB24Burn11GlobalMarker'
PREFIX=ROOT/'research/burn11-global-marker'
def artifact(s):return PREFIX.with_name(PREFIX.name+'-'+s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def exact(p,s):
 if p.exists() and p.read_text()!=s:raise ValueError('Frozen artifact differs: '+str(p))
 if not p.exists():p.write_text(s)
def example(i,row):
 table=';'.join(map(str,codes(row['machine'])));w1,w2,w3=row['weights'][1:]
 args=f"{row['marker_mask']}%N {w1} {w2} {w3} {row['history']} {row['width']} {row['anchor']} {row['fuel']} {row['rounds']}"
 return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline MarkerPotential MarkerState.
From BBB24Burn9ContextMarker Require Import ContextMarker.
From BBB24Burn10MarkerHistory Require Import PartialContextMarker.
From {NS} Require Import GlobalMarker.
Import ListNotations.
Definition machine_{i} := machine_of_codes[{table}].
Lemma old_total_condition_rejected : cm_total machine_{i}=false.
Proof. vm_compute;reflexivity. Qed.
Lemma previous_marker_rule_rejected : pm_check machine_{i} {args}=false.
Proof. vm_compute;reflexivity. Qed.
Lemma global_context_accepted : gm_check machine_{i} {args}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem nonhalt_{i} : NonHalt machine_{i}.
Proof. exact(proj1(gm_check_sound _ _ _ _ _ _ _ _ _ _ global_context_accepted)). Qed.
Theorem state_zero_{i} : QHBound 0 machine_{i}.
Proof. exact(proj2(gm_check_sound _ _ _ _ _ _ _ _ _ _ global_context_accepted)). Qed.
Print Assumptions state_zero_{i}.
'''
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--timeout',type=int,default=600);p.add_argument('--audit-timeout',type=int,default=2400);p.add_argument('--generate-only',action='store_true');args=p.parse_args()
 if min(args.timeout,args.audit_timeout)<=0:p.error('Positive replay budgets required')
 resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));BUILD.mkdir(parents=True,exist_ok=True)
 inp=artifact('proof-input.json');report=artifact('checked.json');invpath=artifact('machines.json')
 old=json.loads(report.read_text())if report.exists()else None;protected={p:sha(p)for p in (report,invpath)if p.exists()}
 data=json.loads(inp.read_text());rows=data['rows'];assert len(rows)==4 and len({r['machine']for r in rows})==4 and data['state_bound']==0
 for row in rows:
  table=codes(row['machine']);assert 16 in table and row['code']==sum(v*17**i for i,v in enumerate(table))
  assert len(row['weights'])==4 and row['weights'][0]==0
 selection=ROOT/data['selection_report'];assert sha(selection)==data['selection_sha256'];assert rows==json.loads(selection.read_text())['rows']
 templates=[ROOT/'proof-sources/burn11-global-marker'/x for x in ('GlobalMarker.v','Regression.v')]
 template_pins={str(p.relative_to(ROOT)):sha(p)for p in templates};assert template_pins==data['template_sha256']
 generic_report=ROOT/'research/burn10-marker-history-checked.json';assert sha(generic_report)==data['generic_report_sha256']
 generic=json.loads(generic_report.read_text())
 for group in ('source_sha256','template_sha256','inputs_sha256','object_sha256'):
  for name,h in generic[group].items():assert sha(ROOT/name)==h,name
 load_paths=[(ROOT/'theories','BBB24'),(original.DEPENDENCY,'BBB24Burn4EntryMarker'),(original.OUTPUT,original.NS),(partial.BUILD,partial.NS),(BUILD,NS)]
 flags=[s for p,ns in load_paths for s in ('-Q',str(p),ns)];files=[]
 for source in templates:
  path=BUILD/source.name;exact(path,source.read_text());files.append(path)
 for i,row in enumerate(rows):
  path=BUILD/f'Example{i:02d}.v';exact(path,example(i,row));files.append(path)
 path=BUILD/'Board.v';exact(path,original.board(rows).replace('From '+original.NS+' Require Import Example','From '+NS+' Require Import Example'));files.append(path)
 descriptor=dict(id='burn11_global_marker',scope='state',rows=4,state_bound=0,instruction_bound=None,module=NS+'.Inventory',board='board',sound='sound',small_sound='small_sound',was_pending='was_pending',proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)),exact_inventory_theorem=NS+'.Inventory.inventory_exact',inventories=[dict(path=str(invpath.relative_to(ROOT)),format='rows')],load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=ns)for p,ns in load_paths[1:]])
 path=BUILD/'Inventory.v';exact(path,inventory_source(dict(descriptor,module=NS+'.Board',machines=[r['machine']for r in rows])));files.append(path)
 sources=dependency_hashes(files,flags)
 for name in ('check_burn11_global_marker.py','check_burn10_marker_history.py','check_burn9_context_marker.py','check_campaign.py','check_shadow_links.py','generate_pipeline_examples.py','kernel_audit_cache_v3.py'):sources['tools/'+name]=sha(ROOT/'tools'/name)
 inputs={str(p.relative_to(ROOT)):sha(p)for p in (inp,selection,generic_report)}
 inventory=json.dumps(dict(rows=[dict(machine=r['machine'])for r in rows]),indent=2)+'\n'
 stable=dict(inputs_sha256=inputs,template_sha256=template_pins,source_sha256=sources,descriptor=descriptor,inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),checked_state_families=4,checked_instruction_families=0)
 if old:assert all(old[k]==v for k,v in stable.items())
 if args.generate_only:print('Exact source regeneration passed; no proof credit.');return
 timings={}
 for path in files:
  start=time.monotonic()
  with path.with_suffix('.log').open('w')as log:subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout,check=True)
  timings[path.stem]=round(time.monotonic()-start,3);print('Compiled '+path.stem+': '+str(timings[path.stem])+'s',flush=True)
 receipt,log=kernel.fresh_paths(BUILD,'kernel-audit');start=time.monotonic();a=kernel.audit([NS+'.Inventory'],[files[-1]],load_paths,receipt,log,recursive=True,timeout=args.audit_timeout)
 assert all(sha(ROOT/n)==h for n,h in {**sources,**inputs,**template_pins}.items());assert all(sha(p)==h for p,h in protected.items())
 current=dict(stable,scope='Four partial-table state-zero census families, all completions; no instruction claim.',compile_seconds=timings,kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),kernel_audit='Full recursive coqchk.',audit_seconds=round(time.monotonic()-start,3),checked_modules=len(a['checked_modules']),reused_modules=len(a['reused_modules']),object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo'))for p in files})
 if old is None:exact(invpath,inventory);exact(report,json.dumps(current,indent=2,sort_keys=True)+'\n')
 (BUILD/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n');print('Four both-state-marker families fully audited.',flush=True)
if __name__=='__main__':main()
