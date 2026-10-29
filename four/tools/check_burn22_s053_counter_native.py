"""Bounded S053 sweep, odd-normalizer, base-case and outer-induction controls; no kernel credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB1RA2LA_2RB3LB3RB1RA'
def run(table,conf,count):
    state,left,head,right=conf
    left,right=list(left),list(right)
    for _ in range(count):
        cell=table[4*state+head]
        write,state=cell//4,cell&1
        if cell&2:
            left=[write]+left
            head,right=(right[0]if right else 0),right[1:]
        else:
            right=[write]+right
            head,left=(left[0]if left else 0),left[1:]
    return state,left,head,right

def front(q,left,right):return q,list(left),(right[0]if right else 0),list(right[1:])
def back(q,left,right):return q,list(left[1:]),(left[0]if left else 0),list(right)


def C(a,b):return back(1,[3]*b,[3]*a+[1])
def main(a,b):return 0,[1]*a+[3]*b,0,[]
def normalize(a,b):
    assert a>=2
    if a>=5:
        if b%2==0:
            t,A,B=normalize(a-3,b+4);return 6*b+7+t,A,B
        t,A,B=normalize(a-3,2*b+3);return 6*b*b+10*b+6+t-3,A,B
    if b%2==0:
        if a==2:return 6*b+14,3,b+1
        if a==3:return 6*b+17,4,b+1
        return 12*b+38,2,b+5
    if a==2:
        if b==1:return 51,4,3
        return 6*b*b-2*b+16,6,2*b-4
    if a==3:return 6*b*b+10*b+13,4,2*b
    return 30*b*b+6*b+38,8,4*b-4

def check():
    table=codes(MACHINE)
    ctx=[[]]+[[a]for a in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    sweeps=pairs=normalizers=bases=outer=0
    for n in range(7):
        for l,r in itertools.product(ctx,repeat=2):
            assert run(table,back(1,[1]*n+[3]+l,r),n+1)==front(0,[1]+l,[3]*n+r)
            assert run(table,back(0,[3]*n+l,r),n)==back(0,l,[2]*n+r)
            assert run(table,front(0,l,[2]*n+r),n)==front(0,[1]*n+l,r)
            assert run(table,front(1,l,[2]*n+r),n)==front(1,[3]*n+l,r)
            assert run(table,back(1,[1,3]*n+l,r),4*n)==back(1,l,[2,2]*n+r)
            assert run(table,back(1,[1,1]*n+l,r),2*n)==back(1,l,[3,3]*n+r)
            sweeps+=6
            assert run(table,back(1,[3]*(2*n)+l,[3,3]+r),10*n)==back(1,l,[3,3]+[2]*(2*n)+r)
            pairs+=1
        for r in ctx:
            assert run(table,back(1,[3]*(2*n),[3,3,3]+r),12*n+7)==back(1,[3]*(2*n+4),r)
            assert run(table,front(0,[1]*(2*n+1)+[3,3,2],[3,3]+r),24*n*n+32*n+15)==back(1,[3]*(4*n+4),[2,2]+r)
            normalizers+=2
        for a in[2,3,4]:
            for b in[2*n,2*n+1]:
                t,A,B=normalize(a,b);assert run(table,C(a,b),t)==main(A,B);bases+=1
    for a in range(2,12):
        for b in range(10):
            t,A,B=normalize(a,b);assert t>=3 and A>=2
            assert run(table,C(a,b),t)==main(A,B);outer+=1
    assert run(table,(0,[],0,[]),51)==main(3,3)
    assert run(table,main(8,1),1235)==main(6,22)
    assert run(table,(0,[3,1],0,[]),13)==(1,[3,3,3,3],0,[])
    assert run(table,back(1,[3,3],[3,1]),10)!=back(1,[],[3,3,2,2])
    # Match the predicted actual closed-grammar cuts in one direct simulation.
    a=b=3;T=51;targets={T:(a,b)}
    while True:
        t,a1,b1=normalize(a,b);T+=a+1+t;a,b=a1,b1
        if T>1000000:next_cut=dict(time=T,a=a,b=b);break
        targets[T]=(a,b)
    tape={};q=head=0
    for t in range(max(targets)+1):
        if t in targets:
            a,b=targets[t];word=[tape.get(x,0)for x in range(head-1,min(tape,default=head)-1,-1)]
            assert q==0 and tape.get(head,0)==0 and word==[1]*a+[3]*b and not any(x>head for x in tape)
        cell=table[4*q+tape.get(head,0)];write=cell//4
        tape[head]=write;head+=1 if cell&2 else -1;q=cell&1
    return dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(table)),state_bound=0,
                arbitrary_context_sweeps=sweeps,pair_iteration_controls=pairs,normalizer_controls=normalizers,
                capped_base_controls=bases,outer_induction_controls=outer,actual_entry_steps=51,
                direct_cuts=[dict(time=t,a=a,b=b)for t,(a,b)in targets.items()],next_cut_prediction=next_cut,
                negative_controls=['arbitrary1/3word31 reaches B0 right blank','changed paired right boundary'])

def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn22-s053-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps({k:v for k,v in row.items()if k!='direct_cuts'}),flush=True)

if __name__=='__main__':main_cli()
