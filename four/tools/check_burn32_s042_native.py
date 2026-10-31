"""S042 exact finite scan and two-counter return controls. Native evidence only."""
import argparse,hashlib,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn32-s042-native.json';MACHINE='1LB2LA3RB2LA_0RB2RA3RA0LA'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def table():return[(int(MACHINE[i]),1 if MACHINE[i+1]=='R'else-1,0 if MACHINE[i+2]=='A'else 1)for i in[0,3,6,9,13,16,19,22]]
def run(T,n,c):
 q,l,h,r=c;l=l[:];r=r[:]
 for _ in range(n):
  w,d,q=T[4*q+h]
  if d==1:l=[w]+l;h=r[0]if r else 0;r=r[1:]
  else:r=[w]+r;h=l[0]if l else 0;l=l[1:]
 return q,l,h,r

def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r

def family(n):return 0,[2,0]+[3]*13+[2,0]+[3]*3+[0]+[3]*(2*n+3)+[0]+[3]*9+[0],0,[]
def F(n,m):return 0,[3]*(2*n+1)+[2,0],0,[2]*(2*m+14)+[0]+[1]*(2*m+1)+[2]*9+[0,1,2,2,0,1,2,0,1,1,1,2,0,1]
def G(n,m):return 0,[0]+[3]*(2*n+17)+[0],2,[2]*(6*m+1)+[1]*(2*n+1)+[2]*9+[0,1,2,2,0,1,2,0,1,1,1,2,0,1]
def hit(T,c,target,budget=10000):
 for n in range(1,budget+1):
  c=run(T,1,c)
  if c==target:return n
 raise AssertionError('Finite control target not reached')
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args();begin=time.monotonic();T=table();assert[4*w+2*(d==1)+q for w,d,q in T]==codes(MACHINE)
 contexts=[[],[0],[1],[2],[3],[0,3],[2,1],[3,2,0]]
 counts=dict(A_odd_context=0,B_zero_context=0,twos_context=0,F_loop=0,G_loop=0,full_return=0,entry=0,unsafe_boundary=0)
 for n in range(7):
  for l in contexts:
   for r in contexts:
    for h in[1,3]:
     assert run(T,n,back(0,[h]*n+l,r))==back(0,l,[2]*n+r);counts['A_odd_context']+=1
    assert run(T,n,front(1,l,[0]*n+r))==front(1,[0]*n+l,r);counts['B_zero_context']+=1
    for q in[0,1]:
     assert run(T,n,front(q,l,[2]*n+r))==front(q^(n%2),[3]*n+l,r);counts['twos_context']+=1
 loop_rows=[]
 for n in range(5):
  for m in range(5):
   a=hit(T,F(n+1,m),F(n,m+1));b=hit(T,G(n+1,m),G(n,m+1));counts['F_loop']+=1;counts['G_loop']+=1
   loop_rows.append(dict(n=n,m=m,F_steps=a,G_steps=b))
 returns=[]
 for n in range(8):
  a=2*n+3;dt=8*a*a+342*a+4467
  assert run(T,dt,family(n))==family(3*n+27);counts['full_return']+=1
  returns.append(dict(n=n,a=a,steps=dt,next_n=3*n+27))
 assert run(T,12565,(0,[],0,[]))==family(42);counts['entry']+=1
 for n in[0,1,9]:
  assert run(T,43+n,(0,[2,0,3,3,3,0],0,[]))==(1,[0]*n+[3,3,3,3,3,2,0,3,0],0,[]);counts['unsafe_boundary']+=1
 assert MACHINE in(ROOT/'build/state-priority/after-audited-standalone78.txt').read_text().splitlines()
 stable=dict(scope='Finite controls only; universal Coq scan soundness and loop induction carry all proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],initial_parameter=42,blank_entry_steps=12565,state_bound=0,
  controls=counts,total_controls=sum(counts.values()),loop_controls=loop_rows,return_controls=returns,
  unsafe_seed=dict(left=[2,0,3,3,3,0],right=[],permanent_B_from=43),
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items());print('S042 native scan, loop, entry and negative controls replayed.')
 else:
  assert not REPORT.exists();REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-begin,6)),indent=2,sort_keys=True)+'\n');print('S042 native controls frozen; native evidence only.')
if __name__=='__main__':main()
