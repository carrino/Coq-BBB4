"""Independent sparse replay of S077's finite B escape; no proof credit."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn19-s077-finite-native.json'
MACHINE='1LB2RB3LA2RA_3RB3LA0LB1LB';ESCAPE=2501552;LAST_A=2501551
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def parse(machine):
 result=[]
 for row in(machine[:12],machine[13:]):
  for i in range(0,12,3):result.append((int(row[i]),1 if row[i+1]=='R'else-1,0 if row[i+2]=='A'else 1))
 return result
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic();table=parse(MACHINE)
 assert[4*w+2*(d==1)+q for w,d,q in table]==codes(MACHINE)
 tape={};pos=q=0;last_A=0;points=[]
 for step in range(ESCAPE+1):
  if q==0:last_A=step
  if step in(0,10000,1000000,LAST_A,ESCAPE):
   support=[x for x,v in tape.items()if v];points.append(dict(step=step,state=q,position=pos,head=tape.get(pos,0),span=[min(support),max(support)]if support else None))
  if step==ESCAPE:break
  write,direction,q=table[4*q+tape.get(pos,0)];tape[pos]=write;pos+=direction
 support={x:v for x,v in tape.items()if v};assert q==1 and tape.get(pos,0)==0 and not any(x>pos for x in support)
 assert last_A==LAST_A and pos==6 and[min(support),max(support)]==[-2741,5]and len(support)==2747
 digest=hashlib.sha256(bytes(support.get(x,0)for x in range(-2741,6))).hexdigest()
 drift_controls=0
 for left_size in range(3):
  for left in itertools.product(range(4),repeat=left_size):
   for zeros in range(5):
    for steps in range(11):
     q0,l0,h0,r0=1,list(left),0,[0]*zeros
     for _ in range(steps):
      w,d,q0=table[4*q0+h0]
      if d==1:l0,h0,r0=[w]+l0,(r0[0]if r0 else 0),r0[1:]
      else:l0,h0,r0=l0[1:],(l0[0]if l0 else 0),[w]+r0
     assert q0==1 and h0==0 and not any(r0)and len(l0)==left_size+steps
     drift_controls+=1
 stable=dict(scope='Independent sparse finite replay and drift controls only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],
  escape_steps=ESCAPE,last_A=LAST_A,state=1,position=6,nonzero_span=[-2741,5],nonzero_cells=2747,final_support_sha256=digest,
  points=points,synthetic_drift_controls=drift_controls,proof_method='Coq computes two Boolean predicates from binary counts; native ending tape is not supplied to the proof.',
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  saved=json.loads(REPORT.read_text());assert all(saved[k]==v for k,v in stable.items());print('Independent S077 prefix and drift controls replayed exactly.')
 else:
  if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
  REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('Independent S077 finite prefix confirms B escape at2501552; no proof credit.')
if __name__=='__main__':main()
