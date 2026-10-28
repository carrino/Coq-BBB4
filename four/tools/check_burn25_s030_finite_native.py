"""S030 compressed finite transcript and independent sparse prefix controls. No proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn25-s030-finite-native.json'
MACHINE='1LB2LA1LA2LB_2RB3RA0LB0LA';ESCAPE=1367354345129;LAST_A=ESCAPE-1

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def table():return[(int(MACHINE[i]),1 if MACHINE[i+1]=='R'else-1,0 if MACHINE[i+2]=='A'else 1)for i in[0,3,6,9,13,16,19,22]]
def Q(a,w):return(0,[3]+[2]*a,w[0]if w else 0,w[1:])
def run(tm,n,c):
 q,l,h,r=c;l=l[:];r=r[:]
 for _ in range(n):
  w,d,q=tm[4*q+h]
  if d==1:l=[w]+l;h=r[0]if r else 0;r=r[1:]
  else:r=[w]+r;h=l[0]if l else 0;l=l[1:]
 return(q,l,h,r)
def transcript():
 a=1;m=c=0;sentinel=False;t=3;rows=[]
 for turn in range(100):
  x=dict(round=turn,step=t,a=a,m=m,sentinel=sentinel,c=c);rows.append(x)
  if m>=2:
   n=m//2;dt=n*(6*a+3)+15*n*n;a+=5*n;m%=2;rule='bulk_pair'
  elif m==0:dt=a+5;m=a;a=1;c=c+1 if sentinel else 1;sentinel=True;rule='zero_or_blank'
  elif sentinel and c>=1:dt=6*a+19;a+=6;m=c-1;c=0;sentinel=False;rule='onezeroone'
  else:break
  t+=dt;x.update(rule=rule,duration=dt)
 assert len(rows)==35 and(a,m,sentinel,c)==(1383582,1,False,0)and t+2==ESCAPE
 return rows

def direct_prefix(tm,rows):
 checks={x['step']:x for x in rows if x['step']<=92898};tape={};pos=q=0;points=[]
 for step in range(92899):
  if step in checks:
   x=checks[step];word=[1]*x['m']+([0]+[1]*x['c']if x['sentinel']else[])
   expected={pos-i-1:v for i,v in enumerate([3]+[2]*x['a'])};expected.update({pos+i:v for i,v in enumerate(word)if v})
   support={p:v for p,v in tape.items()if v};assert q==0 and support==expected,(step,x)
   points.append(dict(step=step,state=q,position=pos,nonzero_cells=len(support),word_sha256=hashlib.sha256(bytes(word)).hexdigest()))
  if step==92898:break
  w,d,q=tm[4*q+tape.get(pos,0)];tape[pos]=w;pos+=d
 return points

def controls(tm):
 contexts=[[]]+[[x]for x in range(4)]+[list(x)for x in itertools.product(range(4),repeat=2)]
 counts=dict(zero=0,pair=0,onezeroone=0,blank=0,bulk=0,binary_B=0,exposed_after2=0,missing_sentinel_negative=0)
 for a in range(13):
  assert run(tm,a+5,Q(a,[]))==Q(1,[1]*a+[0,1]);counts['blank']+=1
  for r in contexts:
   for name,prefix,steps,target in[('zero',[0],a+5,Q(1,[1]*a+[0,1]+r)),('pair',[1,1],6*a+18,Q(a+5,r)),('onezeroone',[1,0,1],6*a+19,Q(a+6,r))]:
    assert run(tm,steps,Q(a,prefix+r))==target;counts[name]+=1
  z=run(tm,1,Q(a,[1]));assert z==(0,[2]*a,3,[2])
  z=run(tm,2,Q(a,[1]));assert z[0]==1 and all(x in[0,2]for x in z[1]+[z[2]]+z[3]);counts['exposed_after2']+=1
 for a in range(9):
  for n in range(13):
   for r in contexts:
    assert run(tm,n*(6*a+3)+15*n*n,Q(a,[1]*(2*n)+r))==Q(a+5*n,r);counts['bulk']+=1
 binary=[[]]+[[x]for x in[0,2]]+[list(x)for x in itertools.product([0,2],repeat=2)]
 for l in binary:
  for r in binary:
   for h in[0,2]:
    for n in range(13):
     q,ll,hh,rr=run(tm,n,(1,l,h,r));assert q==1 and all(x in[0,2]for x in ll+[hh]+rr);counts['binary_B']+=1
 assert run(tm,24,Q(1,[1]))!=Q(6,[]);counts['missing_sentinel_negative']+=1
 return counts

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic();tm=table()
 assert[4*w+2*(d==1)+q for w,d,q in tm]==codes(MACHINE)
 rows=transcript();points=direct_prefix(tm,rows);checks=controls(tm)
 stable=dict(scope='Native compressed transcript and direct sparse prefix/context/boundary controls only. No proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],
  escape_steps=ESCAPE,last_A=LAST_A,macro_edges=34,macro_trace=rows,final_Q=dict(step=1367354345127,a=1383582,word=[1]),permanent_B_reason='After two further steps the whole tape is over{0,2}; B0/B2 preserve that alphabet and stay B.',
  direct_prefix_steps=92898,direct_prefix_checkpoints=points,controls=checks,total_controls=sum(checks.values()),
  proof_method='Universal finite scan programs,34 binary-count macro instantiations, and an infinite binary-tape B invariant. Symbolic repeats/counts remain opaque.',
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items());print('S030 compressed transcript and independent native controls replayed.')
 else:
  assert not REPORT.exists();REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('S030 finite transcript and boundary controls frozen; no proof credit.')
if __name__=='__main__':main()
