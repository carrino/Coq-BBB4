"""Bounded controls for paired carry macros. No formal proof credit."""
from itertools import product
import argparse
import sys,json,hashlib
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
M=['1LB2RA0RA1RA_3RB3LA2LB2LB','1LB2RA0RA1RA_3RB3LA2LB2RB']
def run(tm,c,n):
 q,l,h,r=c;l=l[:];r=r[:]
 for _ in range(n):
  v=tm[4*q+h];w=v//4;q=v&1
  if v&2:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
  else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
 return q,l,h,r
def front(q,l,r):return q,l[:],r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r[:]
def pairs(x,y,n):return[x,y]*n
def encode(ds):return[s for d in ds for s in[1,d]]
def main(k,ds):return 0,[2]+[0]*k+encode(ds)+[1],0,[]
contexts=[[]]+[[a]for a in range(4)]+[list(w)for w in product(range(4),repeat=2)]
rows=[]
for ix,m in enumerate(M):
 tm=codes(m);g=3+2*ix;checks=0
 for n in range(7):
  for l,r in product(contexts,repeat=2):
   assert run(tm,back(1,[2]*n+l,r),n)==back(1,l,[2]*n+r)
   assert run(tm,back(1,[0]*n+l,[2]+r),g*n)==back(1,l,[2]*(n+1)+r)
   assert run(tm,back(1,pairs(1,0,n)+l,r),2*n)==back(1,l,pairs(1,3,n)+r)
   assert run(tm,front(0,l,pairs(1,3,n)+r),2*n)==front(0,pairs(1,2,n)+l,r)
   assert run(tm,front(0,l,[2]*n+r),n)==front(0,[0]*n+l,r)
   for d in[1,2,3]:assert run(tm,back(1,[1,d]+l,r),3)==front(0,[1,{1:2,2:0,3:1}[d]]+l,r)
   checks+=8
 for r in contexts:assert run(tm,back(1,[1],r),7)==front(0,[1,1,1],r)
 assert run(tm,(0,[],0,[]),32+2*ix)==main(2,[1])
 returns=0
 for k in range(7):
  for size in range(6):
   for ds in product(range(4),repeat=size):
    c=next((i for i,d in enumerate(ds)if d),len(ds))
    if c<len(ds):
     target=[2]*c+[{1:2,2:0,3:1}[ds[c]]]+list(ds[c+1:]);cost=(g+1)*k+4*c+7
    else:target=[2]*c+[1];cost=(g+1)*k+4*c+11
    assert run(tm,main(k,ds),cost)==main(k+1,target)
    returns+=1
 # An unchanged boundary2 is essential to the zero sweep's net left motion.
 bad=run(tm,back(1,[0,1],[0]),g)
 assert bad!=back(1,[1],[2,0])
 # Empty carry boundary is not a free arbitrary-left-context macro.
 bad2=run(tm,back(1,[1,1],[2,1]),7)
 assert bad2!=front(0,[1,1,1,1],[2,1])
 rows.append(dict(machine=m,code=sum(v*17**i for i,v in enumerate(tm)),bounce=bool(ix),zero_cost=g,arbitrary_context_checks=checks+len(contexts),main_returns=returns,actual_entry_steps=32+2*ix,initial_main=dict(k=2,ds=[1]),negative_controls=['zero sweep with right-boundary0','empty carry with nonblank left extension']))
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
out=ROOT/'research/burn18-paired-carry-native.json'
data=dict(scope=__doc__,checked_state_families=0,rows=rows,
 source_sha256={str(Path(__file__).relative_to(ROOT)):hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'tools/generate_pipeline_examples.py':hashlib.sha256((ROOT/'tools/generate_pipeline_examples.py').read_bytes()).hexdigest()})
text=json.dumps(data,indent=2,sort_keys=True)+'\n'
if args.check:assert out.read_text()==text
elif out.exists():raise ValueError('Frozen native report exists; use --check')
else:out.write_text(text)
print(json.dumps(rows))
