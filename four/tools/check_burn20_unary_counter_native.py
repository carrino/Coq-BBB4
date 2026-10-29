"""Finite controls for exact frozen S011; universal Coq macros supply proof credit."""
import argparse
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
REPORT=ROOT/'research/burn20-unary-counter-native.json'
MACHINE='1LB0LB2RA2LA_2RB2RA3LB1RB'
def main_cost(n):return 8*n*n+12*n+7
def iteration_cost(m):return 4*m+7
def drain_cost(k,m):return 2*k*k+4*m*k+5*k
def bit(b):return 1 if b else 0
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def mainconf(n):return 0,[2]+[1]*(2*n)+[2],0,[]
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt'
    assert MACHINE in checkpoint.read_text().splitlines()
    table=helper.codes(MACHINE);assert table==[5,1,10,8,11,10,13,7]
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    short=[[]]+[[s]for s in range(4)]
    counts=dict(A_threes=0,B_twos=0,B_threes=0,phase=0,iteration=0,drain=0,finish=0,main_returns=0)
    for n in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,front(0,[2]+l,[3]*n+r),3*n)==front(0,[2]*n+[2]+l,r)
            assert run(table,back(1,[2]*n+l,r),n)==back(1,l,[3]*n+r)
            assert run(table,front(1,l,[3]*n+r),n)==front(1,[1]*n+l,r)
            for key in('A_threes','B_twos','B_threes'):counts[key]+=1
            for b in(False,True):
                assert run(table,front(0,[2]*n+[1]+l,[bit(b)]+r),n+2)==front(0,[2]+l,[3]*n+[bit(not b)]+r)
                counts['phase']+=1
        for r in contexts:
            assert run(table,front(0,[2,2],[3]*(n+1)+[0]+r),5*n+12)==front(0,[2]+[1]*(n+3)+[2],r)
            counts['finish']+=1
    for k,m in itertools.product(range(5),repeat=2):
        for l,r in itertools.product(short,repeat=2):
            for b in(False,True):
                assert run(table,front(0,[2]+[1]*(k+1)+l,[3]*(m+1)+[bit(b)]+r),iteration_cost(m))==front(0,[2]+[1]*k+l,[3]*(m+2)+[bit(not b)]+r)
                outbit=b if k%2==0 else not b
                assert run(table,front(0,[2]+[1]*k+l,[3]*(m+1)+[bit(b)]+r),drain_cost(k,m))==front(0,[2]+l,[3]*(m+k+1)+[bit(outbit)]+r)
                counts['iteration']+=1;counts['drain']+=1
    assert run(table,(0,[],0,[]),3)==mainconf(0)
    for n in range(16):
        assert run(table,mainconf(n),main_cost(n))==mainconf(n+1)
        counts['main_returns']+=1
    a=(main_cost(2)-2*main_cost(1)+main_cost(0))//2
    b=main_cost(1)-main_cost(0)-a;c=main_cost(0)
    da=(drain_cost(2,0)-2*drain_cost(1,0)+drain_cost(0,0))//2
    db=drain_cost(1,0)-da;dc=drain_cost(1,1)-drain_cost(1,0)
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,max_main=15,
        invariant='A0 with nearest-first left word2 1^(2n)2 and blank right tail',
        main_cost=dict(quadratic=a,linear=b,constant=c),main_cost_formula=f'{a}n^2+{b}n+{c}',
        drain_cost=dict(k_squared=da,m_times_k=dc,k_linear=db),
        terminal_rule='one left1 is consumed, one right3 is added, terminal0/1 toggles; empty left run finishes only with terminal0',
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Unary-counter macros and complete returns replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Unary-counter native controls passed; no proof credit.')
if __name__=='__main__':main()
