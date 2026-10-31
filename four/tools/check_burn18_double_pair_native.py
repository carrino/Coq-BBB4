"""Finite paired-counter controls and exact entries; no kernel proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
MACHINES=['1LB2LB1RA0RA_2RB3RA2LB1LA','1LB2LB1RA2RA_2RB3RA2LB1LA']

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
def pairs(x,y,n):return[x,y]*n
def bits(ds):return[s for d in ds for s in([3,1]if d else[1,3])]
def main(k,mode,ds):return 0,[1,1]+pairs(3,1,k)+[1,3 if mode else 1]+bits(ds)+[1,3],0,[]

def check(index,machine):
    table=codes(machine);turn=6-2*index
    contexts=[[]]+[[a]for a in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    checks=0
    for n in range(7):
        for left,right in itertools.product(contexts,repeat=2):
            assert run(table,back(1,pairs(3,1,n)+left,right),2*n)==back(1,left,pairs(2,1,n)+right)
            assert run(table,back(0,pairs(1,3,n)+left,[1]+right),2*n)==back(0,left,[1]+pairs(2,1,n)+right)
            assert run(table,front(0,left,pairs(2,1,n)+right),4*n)==front(0,pairs(1,3,n)+left,right)
            assert run(table,front(0,left,[2]*n+right),n)==front(0,[1]*n+left,right)
            assert run(table,back(1,[3,3]+left,right),turn)==back(1,left,[2,2]+right)
            assert run(table,back(0,[3,1]+left,[1]+right),turn)==front(0,[3]+left,[2,2]+right)
            assert run(table,(0,[1,1]+left,0,right),5)==back(1,left,[2,1,2]+right)
            assert run(table,front(0,left,[2,1,2]+right),5)==front(0,[1,1,3]+left,right)
            checks+=8
    for right in contexts:
        assert run(table,back(0,[],[1]+right),10)==front(0,[1,1,3],right)
        checks+=1
    entry=35-2*index
    assert run(table,(0,[],0,[]),entry)==main(0,False,[])
    returns=0
    for k in range(5):
        for mode in[False,True]:
            for size in range(7):
                for digits in itertools.product([False,True],repeat=size):
                    if not mode:
                        target=list(digits);cost=12*k+24+turn
                    else:
                        carry=next((i for i,d in enumerate(digits)if d),len(digits))
                        if carry<len(digits):
                            target=[True]*carry+[False]+list(digits[carry+1:])
                            cost=12*k+6*carry+26+2*turn
                        else:
                            target=[True]*(carry+1);cost=12*k+6*carry+40+turn
                    assert run(table,main(k,mode,digits),cost)==main(k+1,not mode,target)
                    returns+=1
    if index==0:
        bad=(1,[2],2,[2,1,2]);short=(1,[2],2,[2])
    else:
        bad=(1,[],2,[2,2,1,2]);short=(1,[],2,[2,2])
    assert run(table,(0,[1,1,3,3],0,[]),9-index)==bad
    assert run(table,(0,[1,3],0,[]),7-index)==short
    return dict(machine=machine,code=sum(v*17**i for i,v in enumerate(table)),two=bool(index),
                arbitrary_context_checks=checks,context_max_length=2,repeat_max_length=6,
                main_returns=returns,main_max_k=4,main_max_bits=6,actual_entry_steps=entry,
                initial_main=dict(k=0,mode=False,digits=[]),
                negative_controls=['left1133 reaches B2 with no1/3 on the left',
                                   'left13 reaches B2 with no1/3 on the left'])

def main_cli():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args();rows=[check(i,m)for i,m in enumerate(MACHINES)]
    paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    report=dict(scope=__doc__,checked_state_families=0,rows=rows,
                source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn18-double-pair-native.json'
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps(rows),flush=True)

if __name__=='__main__':main_cli()
