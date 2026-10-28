"""Finite controls for paired20/22 binary counter; no proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'research/burn18-s044-counter-native.json'
MACHINE='1LB2LB0LB0RB_2RB1LB3LB2RA'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(table,conf,count):
 q,l,h,r=conf
 for _ in range(count):
  v=table[4*q+h];w,d,q=v//4,v//2%2,v%2
  if d:l,h,r=[w]+l,(r[0]if r else 0),r[1:]
  else:l,h,r=l[1:],(l[0]if l else 0),[w]+r
 return q,l,h,r
def enc(ds):return[s for d in ds for s in(2,2 if d else 0)]
def auxenc(ds):return[s for d in ds for s in(2 if d else 0,2)]
def value(ds):return sum(d*2**i for i,d in enumerate(ds))
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic();t=codes(MACHINE)
 contexts=[list(w)for n in range(3)for w in itertools.product(range(4),repeat=n)];macros=0
 for n in range(8):
  for l,r in itertools.product(contexts,repeat=2):
   for h in range(3):
    assert run(t,(0,[2]*(2*n)+[2,0]+l,h,r),4*n+4)==(0,enc([0]*n)+[2,2]+l,(h+1)%3,r)
    macros+=1
 for n in range(11):
  assert run(t,(0,[2]*(2*n),0,[]),6*2**n+4*n)==(0,enc([0]*n)+[2,2],1,[])
 for n in range(1,11):
  assert run(t,(0,[2]*(2*n),1,[]),4*n+5)==(0,[2,2]+enc([0]*(n-1))+[2,2],0,[])
 auxiliary_contexts=0
 for n in range(8):
  for l,r in itertools.product(contexts,repeat=2):
   assert run(t,(1,[2]*(2*n)+[0,2]+l,1,r),4*n+2)==(1,auxenc([0]*n)+[2,2]+l,1,r)
   auxiliary_contexts+=1
 auxiliary_drain=0
 for size in range(9):
  for ds in itertools.product((0,1),repeat=size):
   k=next((i for i,d in enumerate(ds)if not d),size)
   if k<size:
    following=[0]*k+[1]+list(ds[k+1:])
    assert 2**size-1-value(ds)==1+(2**size-1-value(following))
   for r in ([],[3,1]):
    conf=(1,auxenc(ds)+[2],1,r);elapsed=0
    while not(conf[0]==0 and conf[2]==1 and conf[3]==r) and elapsed<6*2**size+4*size+4:
     conf=run(t,conf,1);elapsed+=1
    assert conf==(0,enc([0]*size)+[2,2],1,r)
    auxiliary_drain+=1
 count=steps=0
 for size in range(13):
  for ds in itertools.product((0,1),repeat=size):
   head=value(ds)%3
   k=next((i for i,d in enumerate(ds)if not d),size)
   if k<size:following=[0]*k+[1]+list(ds[k+1:]);new_head=(head+1)%3;gap=4*k+4
   else:
    assert head in(0,1)
    following=[0]*size+[1]if head==0 else[1]+[0]*(size-1)+[1]
    new_head=1 if head==0 else 0;gap=6*2**size+4*size if head==0 else 4*size+5
   assert value(following)%3==new_head
   assert run(t,(0,enc(ds),head,[]),gap)==(0,enc(following),new_head,[])
   count+=1;steps+=gap
 assert macros==10584 and count==8191
 assert run(t,(0,[],0,[]),6)==(0,[2,2],1,[])
 assert run(t,(0,[2,2],2,[]),9)!=(0,enc([0,1]),1,[])
 assert run(t,(1,[],1,[]),4)!=(0,[2,2],1,[])
 sources=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
 stable=dict(scope='Finite synthetic controls only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(t)))],
  encoding=['20','22'],checksum='head equals little-endian binary digit value modulo3',
  arbitrary_context_max_length=2,arbitrary_context_macros=macros,outer_macros=21,max_digits=12,main_configurations=count,
  auxiliary_increment_context_macros=auxiliary_contexts,auxiliary_drain_configurations=auxiliary_drain,maximum_auxiliary_digits=8,
  auxiliary_rank='2^length(ds)-1-value(ds)',
  simulated_main_steps=steps,increment_cost='4*carry+4',overflow_cost='head0: 6*2^digits+4*digits; head1: 4*digits+5',
  excluded_corner='all-maximal digits never have checksum2',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources})
 if args.check:
  saved=json.loads(REPORT.read_text());assert all(saved[k]==v for k,v in stable.items());print('All S044 counter controls replayed exactly.')
 else:
  if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
  REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('Native S044 counter controls passed; no proof credit.')
if __name__=='__main__':main()
