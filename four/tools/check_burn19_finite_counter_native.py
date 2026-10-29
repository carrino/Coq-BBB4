"""Finite block controls, direct early cuts, and compressed transcript provenance; no kernel credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB3RA2LA_2RB1RA0LB3LA'
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

def X(a,b):return 0,[3]*a+[2]*b,0,[]
def L(b):return 0,[1]+[2]*b,0,[]
def M(a,b):return 0,[3]*a+[1]+[2]*b,0,[]
def phase(a,r):return 1,[],0,[0]*a+list(r)
def flat(a,b):return 2*b*b+(2*a+1)*b

def check():
    table=codes(MACHINE)
    contexts=[[]]+[[a]for a in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    arbitrary=0
    for n in range(7):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(0,[3]*n+l,r),n)==back(0,l,[2]*n+r)
            assert run(table,front(0,l,[2]*n+r),n)==front(0,[3]*n+l,r)
            assert run(table,back(1,[2]*n+l,r),n)==back(1,l,[0]*n+r)
            assert run(table,front(1,l,[0]*n+r),n)==front(1,[2]*n+l,r)
            assert run(table,back(0,[2]+l,[2]*n+[3]+r),2*n+3)==back(0,l,[2]*(n+2)+r)
            assert run(table,back(0,[2]+l,[2]*n+[1]+r),2*n+3)==back(0,l,[2]*n+[3,2]+r)
            arbitrary+=6
    for a in range(7):
        for b in range(7):
            for r in contexts:
                assert run(table,phase(a,[2]*b+r),flat(a,b))==phase(a+2*b,r)
                arbitrary+=1
    blocks=0
    for a in range(1,26):
        for b in range(26):
            if b>=4:
                assert run(table,X(a,b),8*a+17)==X(a+5,b-4)
            elif b==0:
                assert run(table,X(a,b),2*a*a+12*a+15)==L(2*a+4)
            elif b==1:
                assert run(table,X(a,b),2*a*a+14*a+27)==X(4,2*a+2)
            elif b==2:
                assert run(table,X(a,b),2*a*a+26*a+59)==phase(2*a+9,[])
            else:
                assert run(table,X(a,b),8*a+19)==M(a+4,1)
            blocks+=1
        assert run(table,M(a,1),2*a*a+6*a+29)==X(6,2*a-2)
    for b in range(1,51):
        assert run(table,L(b),5)==M(1,b)
        assert run(table,M(1,b),4*b+33)==X(6,b-1)
    assert run(table,(0,[],0,[]),45)==X(6,0)
    T=45;mode='X';a,b=6,0;rows=[]
    for _ in range(100):
        before=[mode,a,b,T]
        if mode=='X':
            q,r=divmod(b,4)
            if q:
                delta=q*(8*a+17)+20*q*(q-1)
                a,b=a+5*q,r;T+=delta
                rows.append(dict(kind='bulk4',before=before,after=[mode,a,b,T],count=q));continue
            if b==0:delta=2*a*a+12*a+15;mode,a,b='L',0,2*a+4
            elif b==1:delta=2*a*a+14*a+27;a,b=4,2*a+2
            elif b==2:
                delta=2*a*a+26*a+59;T+=delta
                rows.append(dict(kind='drift',before=before,after=['B',0,2*a+9,T]));break
            else:delta=8*a+19;mode,a,b='M',a+4,1
        elif mode=='L':delta=5;mode,a='M',1
        elif a==1:delta=4*b+33;mode,a,b='X',6,b-1
        else:
            assert b==1
            delta=2*a*a+6*a+29;mode,a,b='X',6,2*a-2
        T+=delta;rows.append(dict(kind='boundary',before=before,after=[mode,a,b,T]))
    assert len(rows)==28 and T==1012664081 and rows[-1]['after']==['B',0,34861,1012664081]
    targets={45:['X',6,0,45]}
    for row in rows:
        if row['after'][3]<=1000000:targets[row['after'][3]]=row['after']
    tape={};q=head=0
    for t in range(max(targets)+1):
        if t in targets:
            mode,a,b,_=targets[t]
            word=[tape.get(x,0)for x in range(head-1,min(tape,default=head)-1,-1)]
            expected=X(a,b)[1]if mode=='X'else(L(b)[1]if mode=='L'else M(a,b)[1])
            assert q==0 and tape.get(head,0)==0 and word==expected and not any(x>head for x in tape)
        cell=table[4*q+tape.get(head,0)];write=cell//4
        if write:tape[head]=write
        else:tape.pop(head,None)
        head+=1 if cell&2 else -1;q=cell&1
    return dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(table)),state_bound=4294967296,
                arbitrary_context_checks=arbitrary,block_controls=blocks,mixed_controls=125,
                direct_cuts=len(targets),direct_last_cut=max(targets),drift_time=T,transcript=rows,
                negative_controls=['remainder2 is permanent B drift, not a recurrent counter'])

def main_cli():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn19-finite-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps({k:v for k,v in row.items()if k!='transcript'}),flush=True)

if __name__=='__main__':main_cli()
