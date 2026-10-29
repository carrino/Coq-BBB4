"""Audit local counter macros and synthetic drift controls. No census classification."""
import argparse,hashlib,itertools,json,resource,subprocess,time
from pathlib import Path
from generate_pipeline_examples import codes
from check_campaign import dependency_hashes
import kernel_audit_cache_v3 as kernel
ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn18-counter-obligations/proof'
NS='BBB24Burn18CounterObligations'
PREFIX=ROOT/'research/burn18-counter-obligations'
M56='1LB2LB1RA3RA_3RB3LA2RB2LB'
M59='1LB2LB3RA0RA_2RB3RA2LB3LA'
def artifact(x):return PREFIX.with_name(PREFIX.name+'-'+x)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def exact(p,s):
 if p.exists()and p.read_text()!=s:raise ValueError('Frozen artifact differs:'+str(p))
 if not p.exists():p.write_text(s)
def run(table,conf,count):
 q,l,h,r=conf
 for _ in range(count):
  v=table[4*q+h];w,d,q=v//4,v//2%2,v%2
  if d:l,h,r=[w]+l,(r[0]if r else 0),r[1:]
  else:l,h,r=l[1:],(l[0]if l else 0),[w]+r
 return q,l,h,r
def back(q,l,r):return q,l[1:],(l[0]if l else 0),r
def front(q,l,r):return q,l,(r[0]if r else 0),r[1:]
def native():
 t56,t59=codes(M56),codes(M59)
 contexts=[list(w)for n in range(3)for w in itertools.product(range(4),repeat=n)]
 n56=n59=prefix=0
 for n in range(6):
  for ts in itertools.product((False,True),repeat=n):
   inp=[s for b in ts for s in([1,1]if b else[3])]
   out=[s for b in ts for s in([3,1]if b else[1])]
   for x in(2,3):
    for l,r in itertools.product(contexts,repeat=2):
     assert run(t56,back(1,inp+[1,x]+l,r),2*len(inp)+3)==front(0,out+[3,1 if x==2 else 3]+l,r)
     n56+=1
 for n in range(7):
  for ds in itertools.product((False,True),repeat=n):
   inp=[2 if b else 0 for b in ds];cost=sum(1 if b else 3 for b in ds)
   for l,r in itertools.product(contexts,repeat=2):
    assert run(t59,back(1,inp+l,[2]+r),cost)==back(1,l,[2]*n+[2]+r)
    n59+=1
 for l,r in itertools.product(contexts,repeat=2):
  assert run(t59,(0,[3,3]+l,0,r),4)==(0,[0,0]+l,1,r);prefix+=1
 assert(n56,n59,prefix)==(55566,56007,441)
 assert run(t56,(0,[],0,[]),5)==(0,[3,3],0,[])
 assert run(t59,(0,[],0,[]),18)==(0,[3,3,0,3,2],0,[])
 assert run(t56,(0,[1,3],0,[]),10)==(1,[2,2,3],2,[])
 assert all(run(t56,(1,[2,2,3],2,[]),n)[0]==1 for n in range(101))
 assert run(t59,(0,[3,3],0,[]),5)==(1,[0],0,[2])
 assert run(t59,(0,[3,3,3,0,3,3],0,[]),17)==(1,[0],0,[2,3,2,2,2])
 assert all(run(t59,(1,[0],0,r),n)[0]==1 for r in([2],[2,3,2,2,2])for n in range(101))
 c=run(t56,(0,[],0,[]),101);assert c==(0,[3,1,3,1,1,3,1,2,2,3],1,[])
 wrong=2*sum((x in(1,2))*2**i for i,x in enumerate(c[1]))%3;assert wrong==0
 return dict(scope='Bounded macro controls and excluded synthetic seeds only; no original blank-orbit classification.',
  rows=[dict(machine=m,code=sum(v*17**i for i,v in enumerate(codes(m))))for m in(M56,M59)],
  arbitrary_context_max_length=2,s56_token_prefix_max_tokens=5,s56_carry_controls=n56,
  s59_binary_sweep_max_cells=6,s59_sweep_controls=n59,s59_prefix_controls=prefix,
  s56_wrong_checksum_actual_step=101,s56_wrong_checksum_expected_head=wrong,s56_actual_head=c[2],
  excluded_synthetic_seeds=[dict(machine=M56,left=[1,3],head=0,guard_step=10,result=[1,[2,2,3],2,[]]),
   dict(machine=M59,left=[3,3],head=0,guard_step=5,result=[1,[0],0,[2]]),
   dict(machine=M59,left=[3,3,3,0,3,3],head=0,guard_step=17,result=[1,[0],0,[2,3,2,2,2]])],
  new_state_families=0,new_instruction_families=0)
def tables_source():
 txt=f'From Coq Require Import List.\nFrom BBB24 Require Import Statement Pipeline.\nFrom {NS} Require Import CounterObligations.\nImport ListNotations.\n'
 for short,m in(('s56',M56),('s59',M59)):
  txt+=f'Lemma exact_{short}_table : forall q s,{short}_tm q s=machine_of_codes[{";".join(map(str,codes(m)))}]q s.\nProof. intros q s;destruct q,s;reflexivity. Qed.\n'
 return txt
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');p.add_argument('--timeout',type=int,default=600);p.add_argument('--audit-timeout',type=int,default=3600);args=p.parse_args()
 if min(args.timeout,args.audit_timeout)<=0:p.error('Positive budgets required')
 resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));BUILD.mkdir(parents=True,exist_ok=True)
 hypothesis=artifact('hypotheses.json');assert{r['machine']for r in json.loads(hypothesis.read_text())['selected']}=={M56,M59}
 native_path=artifact('native.json');controls=native();exact(native_path,json.dumps(controls,indent=2,sort_keys=True)+'\n')
 template=ROOT/'proof-sources/burn18-counter-obligations/CounterObligations.v';out=BUILD/template.name;exact(out,template.read_text())
 tables=BUILD/'ExactTables.v';exact(tables,tables_source());files=[out,tables]
 load_paths=[(ROOT/'theories','BBB24'),(BUILD,NS)];flags=kernel._loadargs(load_paths)
 sources=dependency_hashes(files,flags)
 for name in('check_burn18_counter_obligations.py','generate_pipeline_examples.py','check_campaign.py','check_shadow_links.py','kernel_audit_cache_v3.py'):sources['tools/'+name]=sha(ROOT/'tools'/name)
 stable=dict(scope='Audited universal local macros, actual finite entries, and synthetic drift theorems only. Both original census families remain unclassified.',
  inputs_sha256={str(x.relative_to(ROOT)):sha(x)for x in(hypothesis,native_path)},template_sha256={str(template.relative_to(ROOT)):sha(template)},source_sha256=sources,
  new_state_families=0,new_instruction_families=0,rows=controls['rows'],module=NS+'.ExactTables')
 report_path=artifact('checked.json');old=json.loads(report_path.read_text())if report_path.exists()else None
 if old:assert all(old[k]==v for k,v in stable.items())
 if args.check:
  assert old is not None
  for group in('inputs_sha256','template_sha256','source_sha256','object_sha256'):
   for name,h in old[group].items():assert sha(ROOT/name)==h
  receipt=ROOT/old['kernel_receipt'];assert sha(receipt)==old['kernel_receipt_sha256'];validation=kernel.ReceiptValidation();r=validation.load(receipt)
  assert kernel.snapshot([tables],load_paths)==r['snapshot'];validation.recheck()
  assert r['kind']=='recursive'and r['parents']==[]and r['reused_modules']==[]and NS+'.CounterObligations'in r['checked_modules']
  print('Local macros, synthetic drift controls and current recursive receipt revalidated; zero classifications.');return
 timings={}
 for f in files:
  start=time.monotonic()
  with f.with_suffix('.log').open('w')as log:subprocess.run(['coqc','-native-compiler','no',*flags,str(f)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
  timings[f.stem]=round(time.monotonic()-start,3)
 receipt,log=kernel.fresh_paths(BUILD,'kernel-audit');start=time.monotonic()
 audit=kernel.audit([NS+'.ExactTables'],[tables],load_paths,receipt,log,recursive=True,timeout=args.audit_timeout)
 assert NS+'.CounterObligations'in audit['checked_modules']
 assert all(sha(ROOT/name)==h for name,h in{**stable['inputs_sha256'],**stable['template_sha256'],**sources}.items())
 result=dict(stable,compile_seconds=timings,audit_seconds=round(time.monotonic()-start,3),checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
  kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),object_sha256={str(f.with_suffix('.vo').relative_to(ROOT)):sha(f.with_suffix('.vo'))for f in files})
 if old is None:exact(report_path,json.dumps(result,indent=2,sort_keys=True)+'\n')
 (BUILD/'current-proof-receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print('Universal local macros and synthetic drift controls fully audited; zero classifications.')
if __name__=='__main__':main()
