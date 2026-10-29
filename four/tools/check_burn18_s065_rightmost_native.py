"""Finite controls for the rightmost-marker invariant and B returns; no proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn18-s065-rightmost-native.json'
MACHINE='1LB2RA0LB1RA_1RB3LB2LB0RA'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def step(table,c):
 q,l,h,r=c;v=table[4*q+h];w,d,q=v//4,v//2%2,v%2
 return(q,[w]+l,(r[0]if r else 0),r[1:])if d else(q,l[1:],(l[0]if l else 0),[w]+r)
def run(table,c,n):
 for _ in range(n):c=step(table,c)
 return c
def inv(c):
 q,l,h,r=c;nonzero=[s for s in[h]+r if s]
 return(nonzero[-1]in(1,3))if nonzero else q==0
def reaches_A(table,c,budget=100):
 for n in range(budget+1):
  if c[0]==0:return n
  c=step(table,c)
 raise ValueError('B return budget exceeded')
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic();t=codes(MACHINE)
 contexts=[list(w)for n in range(3)for w in itertools.product(range(4),repeat=n)];right_contexts=[list(w)for n in range(4)for w in itertools.product(range(4),repeat=n)]
 preservation=returns=0;max_return=0
 for q,h,l,r in itertools.product(range(2),range(4),contexts,contexts):
  c=(q,l,h,r)
  if inv(c):assert inv(step(t,c));preservation+=1
 for h,l,r in itertools.product((1,2,3),contexts,contexts):max_return=max(max_return,reaches_A(t,(1,l,h,r)));returns+=1
 zero_returns=0
 for l,r in itertools.product(contexts,right_contexts):
  if inv((1,l,0,r)):
   max_return=max(max_return,reaches_A(t,(1,l,0,r)));zero_returns+=1
 assert inv((0,[],0,[]))and run(t,(0,[],0,[]),7)==(0,[1,0,1],0,[])
 assert not inv((0,[0],2,[]))and run(t,(0,[0],2,[]),2)==(1,[1],0,[])
 assert all(run(t,(1,[],0,[]),n)==(1,[1]*n,0,[])for n in range(101))
 stable=dict(scope='Bounded invariant and arbitrary-context return controls only; no independent proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(t)))],
  invariant='Rightmost nonzero of head/right suffix is1or3, or suffixallzero andstateA.',left_and_right_max_length=2,
  invariant_steps=preservation,nonzero_B_returns=returns,zero_B_right_context_max_length=3,zero_B_returns=zero_returns,max_return_steps=max_return,
  actual_entry=dict(step=7,left=[1,0,1],head=0),excluded_seed=dict(state='A',left=[0],head=2,right=[],steps=2,result=[1,[1],0,[]]),
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  saved=json.loads(REPORT.read_text());assert all(saved[k]==v for k,v in stable.items());print('All S065 rightmost-marker and B-return controls replayed exactly.')
 else:
  if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
  REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('S065 rightmost-marker native controls passed; no proof credit.')
if __name__=='__main__':main()
