"""Finite controls for the S014 guarded grammar closure; zero proof credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
PREFIX=ROOT/'research/burn39-s014-normalizer'
MACHINES=('1LB0RA0LB2RB_3RB3LA0LB1RA','1LB0RA0LB2RB_3RB3LA0RA1RA','1LB0RA0LB2RB_3RB3LA1RA1RA')
WORDS=('13312','012','312','13313312');FW='31313'
def artifact(s):return PREFIX.with_name(PREFIX.name+'-'+s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def enc(ts):return ''.join(WORDS[t]for t in ts)
def F(ts):
    if not ts:return[0,1]
    t,*xs=ts
    return [0]+F(xs)if t==0 else[3]+xs if t==1 else[1]+F(xs)if t==2 else[0,0,2]+xs
def cost(ts):
    if not ts:return 30
    t,*xs=ts
    return 38+cost(xs)if t==0 else 10 if t==1 else 26+cost(xs)if t==2 else 46
def decode(m):
    s=m.replace('_','')
    return[(int(s[i]),1 if s[i+1]=='R'else -1,ord(s[i+2])-65)for i in range(0,24,3)]
def step(T,c):
    q,l,h,r=c;w,d,q=T[4*q+h]
    return(q,[w]+l,r[0]if r else 0,r[1:])if d==1 else(q,l[1:],l[0]if l else 0,[w]+r)
def back(w,r):
    w=list(map(int,w));return(1,w[1:],w[0]if w else 0,list(map(int,r)))
def cut(w):return(0,list(map(int,w)),0,[])
def maincut(ts):return cut(enc(list(ts))+'3')
def run(T,c,n):
    for _ in range(n):c=step(T,c)
    return c
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    inp=artifact('native-input.json');din=json.loads(inp.read_text());assert tuple(din['machines'])==MACHINES
    frontier=ROOT/din['frontier_source'];assert sha(frontier)==din['frontier_sha256'];assert MACHINES[0]in frontier.read_text().splitlines()
    words=[list(ts)for n in range(din['maximum_token_length']+1)for ts in itertools.product(range(4),repeat=n)]
    T=decode(MACHINES[0]);values=[4*w+(2 if d==1 else 0)+q for w,d,q in T];assert values==codes(MACHINES[0])
    controls=[]
    def control(ts,out,n,kind):
        assert out[0]==0 and(len(out)==1 or out[1]in(0,1,3))
        actual=run(T,maincut(ts),n);assert actual==maincut(out),(ts,out,n,actual)
        controls.append(dict(kind=kind,input=ts,output=out,steps=n))
    control([0],[0,3,0,1],444,'single_a')
    for xs in words:
        control([0,1]+xs,[0,0,2]+F(xs),354+cost(xs),'ab')
        control([0,3]+xs,[0,0,1]+F(F(xs)),522+cost(xs)+cost(F(xs)),'ad')
        f3=F(F(F(xs)));assert f3[:2]==[0,0];ys=f3[2:]
        n=220+cost(xs)+cost(F(xs))+cost(F(F(xs)))+110+cost(ys)+cost(F(ys))
        control([0,0]+xs,[0]+F(F(ys)),n,'aa')
    assert run(T,(0,[],0,[]),56)==maincut([0,1])
    negatives=[]
    for v,m in enumerate(MACHINES):
        Tn=decode(m);assert[4*w+(2 if d==1 else 0)+q for w,d,q in Tn]==codes(m)
        for n in range(6):
            out=run(Tn,cut('12'+'13'*(4*n+3)+'3'),192*n+231);q,l,h,r=out;assert(q,h,r)==(1,0,[])
            for k in range(65):
                assert out==(1,[3]*k+l,0,[]);out=step(Tn,out)
            negatives.append(dict(variant=v,n=n,escape_steps=192*n+231,drift_checks=65))
    out=run(T,maincut([0,2]),225);q,l,h,r=out;assert(q,h,r)==(1,0,[])
    for k in range(65):
        assert out==(1,[3]*k+l,0,[]);out=step(T,out)
    data=dict(scope='Independent finite guarded-return and negative-boundary controls; zero proof credit.',
        rows=[dict(machine=MACHINES[0],code=sum(v*17**i for i,v in enumerate(values)))],tokens=list(WORDS),
        guarded_return_controls=controls,guarded_return_count=len(controls),maximum_macro_steps=max(c['steps']for c in controls),
        paired_negative_controls=negatives,rejected_ac_seed_steps=225,negative_drift_checks=65,actual_blank_entry_steps=56,
        inputs_sha256={str(p.relative_to(ROOT)):sha(p)for p in(inp,frontier)},
        source_sha256={str(p.relative_to(ROOT)):sha(p)for p in(Path(__file__),ROOT/'tools/generate_pipeline_examples.py')},
        checked_state_families=0,checked_instruction_families=0)
    data=json.loads(json.dumps(data));report=artifact('native.json')
    if args.check:assert json.loads(report.read_text())==data
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(guarded_returns=len(controls),paired_negatives=len(negatives),rejected_ac_seed=1)),flush=True)
if __name__=='__main__':main()
