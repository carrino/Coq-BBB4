"""Compressed S032 cut transcript and independent direct prefix controls. No proof credit."""
import argparse,hashlib,json,time
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1];REPORT=ROOT/'research/burn21-s032-finite-native.json'
MACHINE='1LB2LA1RA2RB_2RB3LB0LB1LA';ESCAPE=67093892759901295;LAST_A=ESCAPE-1

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def transcript():
 mode='C';a=k=j=t=0;b=None;rows=[]
 for turn in range(100):
  row=dict(round=turn,step=t,mode=mode,a=a,k=k,b=b,j=j);rows.append(row)
  if mode=='Q':
   assert b is None and k==0 and j==0
   dt=a+6;k=a-1;a=2;b=1;mode='C';rule='Qblank'
  else:
   n=k//2
   if n:dt=n*(2*a+16)+5*n*n;a+=5*n;k%=2;rule='bulk'
   elif b is None:
    if k==1:break
    dt=2*a+22;k=a+2;a=2;b=1;rule='blank'
   elif k==0 and b==1:dt=2*a+17;a+=4;k=j;b=None;j=0;rule='one'
   elif k==0 and b==0:dt=2*a+22;k=a+2;a=2;b=1;rule='zero'
   elif k==1 and b==1:dt=2*a+24;k=a+2;a=2;b=0;j+=1;rule='three_one'
   else:
    assert k==1 and b==0 and j==1
    dt=a+22;a+=6;k=0;j=0;b=None;mode='Q';rule='bridge303'
  t+=dt;row.update(rule=rule,duration=dt)
 assert len(rows)==54 and(mode,a,k,b,j)==('C',530843041,1,None,0)
 assert t+a+14==ESCAPE and t==67093892229058240
 return rows

def direct_controls(rows):
 # Parse independently from encoded transition integers used by the Coq table.
 tm=[]
 for row in(MACHINE[:12],MACHINE[13:]):
  for i in range(0,12,3):tm.append((int(row[i]),1 if row[i+1]=='R'else-1,0 if row[i+2]=='A'else 1))
 assert[4*w+2*(d==1)+q for w,d,q in tm]==codes(MACHINE)
 checks={x['step']:x for x in rows if x['step']<=491443}
 tape={};pos=q=0;points=[]
 for step in range(491444):
  if step in checks:
   x=checks[step];assert x['mode']=='C'and q==0 and tape.get(pos,0)==0
   right=[2]*x['a']+[3]*x['k']+([]if x['b']is None else[x['b']]+[3]*x['j'])
   support={p:v for p,v in tape.items()if v};expected={pos+i+1:v for i,v in enumerate(right)if v}
   assert support==expected,(step,x)
   points.append(dict(step=step,state=q,position=pos,nonzero_cells=len(support),word_sha256=hashlib.sha256(bytes(right)).hexdigest()))
  if step==491443:break
  w,d,q=tm[4*q+tape.get(pos,0)];tape[pos]=w;pos+=d
 # Guard control: a singleton terminal3 reaches the dangerous B0 boundary.
 controls=0
 for a in range(13):
  cells={p+1:2 for p in range(a)};cells[a+1]=3;p=q=0
  for _ in range(a+14):w,d,q=tm[4*q+cells.get(p,0)];cells[p]=w;p+=d
  assert q==1 and cells.get(p,0)==0 and not any(v for x,v in cells.items()if x>p)
  controls+=1
 return points,controls

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args();start=time.monotonic()
 rows=transcript();points,guards=direct_controls(rows)
 stable=dict(scope='Compressed transcript from universal cut formulas; independent direct sparse prefix and terminal guard controls. No proof credit.',
  rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(codes(MACHINE))))],escape_steps=ESCAPE,last_A=LAST_A,
  macro_edges=53,macro_trace=rows,direct_prefix_steps=491443,direct_prefix_checkpoints=points,synthetic_exposed_three_controls=guards,
  final_cut=dict(step=67093892229058240,accumulator=530843041,right=[3]),
  final_symbolic_left='2 :: 1^530843044',proof_method='53 binary-count instantiations of universally proved cut macros; symbolic repeats and counts remain opaque.',
  source_sha256={str(x.relative_to(ROOT)):sha(x)for x in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')})
 if args.check:
  old=json.loads(REPORT.read_text());assert all(old[k]==v for k,v in stable.items());print('S032 compressed transcript and independent sparse controls replayed.')
 else:
  assert not REPORT.exists();REPORT.write_text(json.dumps(dict(stable,seconds=round(time.monotonic()-start,6)),indent=2,sort_keys=True)+'\n');print('S032 finite escape selected by53 compressed macro edges; no proof credit.')
if __name__=='__main__':main()
