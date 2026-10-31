"""Independent S066 sparse entry and sliding-frontier controls. No proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn28-s066-frontier-native.json';MACHINE='1LB2RA0LB1RB_3RB3LA1LA2RA';ENTRY=1922128;P=[2,2,1,1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def tm():return[(int(MACHINE[i]),1 if MACHINE[i+1]=='R'else-1,0 if MACHINE[i+2]=='A'else 1)for i in[0,3,6,9,13,16,19,22]]
def run(T,n,c):
 q,l,h,r=c;l=l[:];r=r[:]
 for _ in range(n):
  w,d,q=T[4*q+h]
  if d==1:l=[w]+l;h=r[0]if r else 0;r=r[1:]
  else:r=[w]+r;h=l[0]if l else 0;l=l[1:]
 return q,l,h,r
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args();start=time.monotonic();T=tm();assert[4*w+2*(d==1)+q for w,d,q in T]==codes(MACHINE)
 tape={};q=pos=0;points=[]
 for t in range(ENTRY+11*20+1):
  if t>=ENTRY and(t-ENTRY)%11==0:
   support={x:v for x,v in tape.items()if v};left=[tape.get(pos-i-1,0)for i in range(4)]
   assert q==0 and tape.get(pos,0)==0 and left==P and not any(x>pos for x in support)
   assert pos==10+(t-ENTRY)//11
   points.append(dict(step=t,position=pos,left_prefix=left,nonzero_cells=len(support),nonzero_span=[min(support),max(support)]))
  if t==ENTRY+11*20:break
  w,d,q=T[4*q+tape.get(pos,0)];tape[pos]=w;pos+=d
 lefts=[list(x)for n in range(4)for x in itertools.product(range(4),repeat=n)];rights=[list(x)for n in range(3)for x in itertools.product(range(4),repeat=n)]
 counts=dict(slide_both_contexts=0,positive_returns=0,B_after_one=0,prefix_negative=0,rightblank_negative=0)
 for l in lefts:
  for r in rights:
   assert run(T,11,(0,P+l,0,r))==(0,P+[2]+l,r[0]if r else 0,r[1:]);counts['slide_both_contexts']+=1
  for n in range(13):
   assert run(T,11*n,(0,P+l,0,[]))==(0,P+[2]*n+l,0,[]);counts['positive_returns']+=1
  assert run(T,1,(0,P+l,0,[]))==(1,[2,1,1]+l,2,[1]);counts['B_after_one']+=1
 assert run(T,11,(0,[2,2,1,2],0,[]))!=(0,P+[2],0,[]);counts['prefix_negative']+=1
 assert run(T,11,(0,P,0,[1]))!=(0,P+[2],0,[]);counts['rightblank_negative']+=1
 stable=dict(scope='Independent sparse original prefix and finite sliding-frontier context controls only; zero proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],entry_step=ENTRY,left_prefix=P,entry_state=0,entry_head=0,entry_rightblank=True,frontier_step=11,points=points,controls=counts,total_controls=sum(counts.values()),proof_method='Coq checks only the finite prefix predicate; universal11-step return proves both-state recurrence with arbitrary left tail.',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items());print('S066 sparse entry and sliding controls replayed.')
 else:
  assert not REPORT.exists();REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('S066 entry and sliding controls frozen; native evidence only.')
if __name__=='__main__':main()
