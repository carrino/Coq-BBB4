"""S074 binary-even cut grammar and universal program controls. Native evidence only."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn29-s074-even-counter-native.json';MACHINE='1LB2RB0LA1RB_2RB3RA1LA0LB'
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
def wall(ns):return sum(([3]+[2]*(n+1)for n in ns),[])
def cost(a,ns):return a+3 if not ns else 4*a+8+cost(a+ns[0],ns[1:])
def output(a,ns,r):return[0]*(a+sum(ns))+[1,0,1]+[1]*(2*len(ns))+r
def even(w):return all(x in[0,1]for x in w)and sum(w)%2==0
def cut_return(T,w):
 q=h=p=0;l=[];r=w[:]
 for t in range(1,100000):
  v,d,q=T[4*q+h]
  if d==1:l=[v]+l;h=r[0]if r else 0;r=r[1:];p+=1
  else:r=[v]+r;h=l[0]if l else 0;l=l[1:];p-=1
  if q==0 and h==0 and not l:return t,r,p
 raise AssertionError('Native budget exhausted')
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args();start=time.monotonic();T=table();assert[4*w+2*(d==1)+q for w,d,q in T]==codes(MACHINE)
 contexts=[list(x)for n in range(3)for x in itertools.product(range(4),repeat=n)]
 counts=dict(drop1=0,merge=0,wall_unwind=0,forward=0,even_cut_words=0,odd_negative=0,wall_negative=0)
 for a in range(9):
  for l in contexts:
   for r in contexts:
    assert run(T,2*a+3,(0,[3]+[2]*a+[1]+l,0,r))==(0,[3]+[2]*a+l,0,[1]+r);counts['drop1']+=1
    assert run(T,4*a+8,(0,[3]+[2]*(a+1)+[3,2]+l,0,r))==(0,[3]+[2]*(a+1)+l,0,[1,1]+r);counts['merge']+=1
 for a in range(5):
  for length in range(4):
   for ns0 in itertools.product(range(3),repeat=length):
    ns=list(ns0)
    for r in contexts:
     assert run(T,cost(a,ns),(0,wall([a]+ns),0,r))==(0,[],0,output(a,ns,r));counts['wall_unwind']+=1
 for n in range(9):
  for a in range(5):
   for ns in[[],[0],[2,1]]:
    for r in contexts:
     assert run(T,n+2,front(0,wall([a]+ns),[1]+[0]*n+[1]+r))==front(0,wall([n,a]+ns),r);counts['forward']+=1
 longest=0
 for length in range(11):
  for word in itertools.product([0,1],repeat=length):
   w=list(word)
   if not even(w):continue
   dt,v,p=cut_return(T,w);assert even(v)and p==-2 and dt>0;counts['even_cut_words']+=1;longest=max(longest,dt)
 for n in range(21):
  assert run(T,4+n,(0,[],0,[1]))==(1,[2]*n+[2,3,2],0,[]);counts['odd_negative']+=1
 assert run(T,3,(0,[3],0,[]))!=(0,[],0,[1,0,1]);counts['wall_negative']+=1
 w=[];t=p=0;points=[dict(step=0,position=0,right_length=0,ones=0)]
 for _ in range(64):
  dt,w,dp=cut_return(T,w);t+=dt;p+=dp;assert even(w);points.append(dict(step=t,position=p,right_length=len(w),ones=sum(w),right_sha256=hashlib.sha256(bytes(w)).hexdigest()))
 ruler=[0,6,28,34,86,92,114,120,230,236,258,264,316,322,344,350,574]
 assert[x['step']for x in points[:len(ruler)]]==ruler
 stable=dict(scope='Finite controls for universal binary-even cut grammar and parser/wall programs only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],initial_word=[],controls=counts,total_controls=sum(counts.values()),longest_control_return=longest,original_frontier_points=points,
  odd_boundary=dict(input=[1],permanent_B_from=4),proof_method='Forward word-length induction and finite wall-length induction prove positive returns for every binary-even word; initial empty word needs no finite simulation.',
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items());print('S074 binary-even grammar and native program controls replayed.')
 else:
  assert not REPORT.exists();REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('S074 grammar/program controls frozen; native evidence only.')
if __name__=='__main__':main()
