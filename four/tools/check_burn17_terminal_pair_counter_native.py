"""Finite controls for a binary prefix with three terminal forms; no proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'research/burn17-terminal-pair-counter-native.json'
MACHINE='1LB2LB0LB2RB_1RB2RA3LB1RA'
TAILS=([1,1],[2,1],[2]);BASE=(2,0,1)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(table,conf,count):
 q,l,h,r=conf
 for _ in range(count):
  v=table[4*q+h];w,d,q=v//4,v//2%2,v%2
  if d:l,h,r=[w]+l,(r[0]if r else 0),r[1:]
  else:l,h,r=l[1:],(l[0]if l else 0),[w]+r
 return q,l,h,r
def enc(ds):return[s for d in ds for s in(2 if d else 1,2)]
def head(ds,t):return(sum(d*2**i for i,d in enumerate(ds))+2**len(ds)*BASE[t])%3
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic();table=codes(MACHINE)
 contexts=[list(w)for n in range(3)for w in itertools.product(range(4),repeat=n)];macros=0
 for n in range(8):
  for l,r in itertools.product(contexts,repeat=2):
   for h in range(3):
    for x in range(4):
     assert run(table,(0,[2]*(2*n)+[1,x]+l,h,r),4*n+2)==(0,enc([0]*n)+[2,x]+l,(h+1)%3,r)
     macros+=1
 outer=0
 for n in range(11):
  for h in range(3):
   assert run(table,(0,[2]*(2*n+1),h,[]),4*n+4)==(0,enc([0]*n)+[1,1],(h+1)%3,[]);outer+=1
  assert run(table,(0,[2]*(2*n)+[2,1],0,[]),4*n+5)==(0,enc([1]+[0]*n)+[2],0,[]);outer+=1
 for n in range(1,11):
  assert run(table,(0,[2]*(2*n)+[2,1],1,[]),4*n+9)==(0,enc([0,1]+[0]*(n-1))+[2],0,[]);outer+=1
 count=steps=0
 for size in range(11):
  for ds in itertools.product((0,1),repeat=size):
   for t in range(3):
    h=head(ds,t);k=next((i for i,d in enumerate(ds)if not d),size)
    if k<size:following=[0]*k+[1]+list(ds[k+1:]);new_t=t;new_head=(h+1)%3;gap=4*k+2
    elif t==0:
     assert h==2;following=[0]*size;new_t=1;new_head=0;gap=4*size+2
    elif t==1:
     assert h in(0,1);following=[1]+[0]*size if h==0 else[0,1]+[0]*(size-1)
     new_t=2;new_head=0;gap=4*size+(5 if h==0 else 9)
    else:following=[0]*size;new_t=0;new_head=(h+1)%3;gap=4*size+4
    assert head(following,new_t)==new_head
    assert run(table,(0,enc(ds)+TAILS[t],h,[]),gap)==(0,enc(following)+TAILS[new_t],new_head,[])
    count+=1;steps+=gap
 assert macros==42336 and outer==54 and count==6141
 assert run(table,(0,[],0,[]),3)==(0,[2,1],0,[])
 assert run(table,(0,[2,1],2,[]),5)!=(0,[2,2,2],0,[])
 sources=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
 stable=dict(scope='Finite synthetic controls only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(table)))],
  encoding=['12','22'],terminal_forms=['11','21','2'],terminal_values=[2,0,1],
  checksum='binary prefix value plus2^prefix_length times terminal value, modulo3',
  arbitrary_context_max_length=2,arbitrary_context_macros=macros,outer_macros=outer,max_prefix_digits=10,main_configurations=count,
  simulated_main_steps=steps,increment_cost='4*carry+2',
  excluded_corner='all-maximal prefix with terminal21 never has checksum2',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources})
 if args.check:
  saved=json.loads(REPORT.read_text());assert all(saved[k]==v for k,v in stable.items());print('All terminal-pair counter controls replayed exactly.')
 else:
  if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
  REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('Native terminal-pair counter controls passed; no proof credit.')
if __name__=='__main__':main()
