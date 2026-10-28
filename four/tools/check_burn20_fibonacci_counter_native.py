"""Finite exact-table controls for S022; universal Coq return macros supply proof credit."""
import argparse
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
REPORT=ROOT/'research/burn20-fibonacci-counter-native.json'
MACHINE='1LB1RA1LB2RB_3RB3LA3LB2RA'
def main_cost(m,n):return 8*m*n+12*n*n+20*m+44*n+37
def drain_cost(m,n):return 8*m*n+12*n*n+22*n
def nextparams(m,n):return n+2,m+n
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def mainconf(m,n):return 0,[2]*(2*m)+[1]+[2]*(2*n+1)+[3],0,[]
def qconf(m,n,k):return 0,[2]*(2*m)+[1]+[2]*(2*n+1),2,[3]*(2*k+1)
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def coefficients(f):
    c=f(0,0);ml=f(1,0)-c;nq=(f(0,2)-2*f(0,1)+c)//2
    return dict(m_times_n=f(1,1)-f(1,0)-f(0,1)+c,n_squared=nq,m_linear=ml,n_linear=f(0,1)-c-nq,constant=c)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert MACHINE in checkpoint.read_text().splitlines()
    table=helper.codes(MACHINE);assert table==[5,6,5,11,15,12,13,10]
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    short=[[]]+[[s]for s in range(4)]
    counts={key:0 for key in ['left_twos','right_pairs','A_one_even','A_one_odd','to_left','wall_even','wall_odd','open_zero','open_odd','open_even_step','open_even','wall_round','open_round','Q_pair','drain','Q_finish','main_returns']}
    for n in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(1,[2]*n+l,r),n)==back(1,l,[3]*n+r)
            assert run(table,front(0,l,[3]*(2*n)+r),2*n)==front(0,[2]*(2*n)+l,r)
            assert run(table,front(0,l,[1]+[3]*(2*n)+r),2*n+1)==front(0,[2]*(2*n)+[1]+l,r)
            assert run(table,front(0,l,[1]+[3]*(2*n+1)+[1]+r),2*n+3)==front(0,[2]*(2*n)+[1]+l,[2,3]+r)
            assert run(table,front(0,[2]*(2*n)+[3]+l,[2]+r),4*n+2)==front(0,[2]*(2*n+1)+l,[1]+r)
            assert run(table,front(0,[2]*(2*n+1)+[3]+l,[2]+r),4*n+5)==front(0,[2]*(2*n+1)+l,[2,3]+r)
            for key in ['left_twos','right_pairs','A_one_even','A_one_odd','wall_even','wall_odd']:counts[key]+=1
            for h in(0,2):
                assert run(table,(0,[2]*n+[1]+l,h,r),n+2)==back(0,l,[3]*(n+1)+[1]+r)
                counts['to_left']+=1
        for r in contexts:
            assert run(table,front(0,[],[2]+r),3)==front(0,[],[3,3]+r)
            assert run(table,front(0,[2]*(2*n+1),[2]+r),4*n+4)==front(0,[2]*(2*n+1)+[3],[1]+r)
            assert run(table,front(0,[2]*(2*n+2),[2]+r),4*n+7)==front(0,[2]*(2*n+1)+[3],[2,3]+r)
            assert run(table,front(0,[2]*(2*n+2),[2]+r),12*n+16)==front(0,[2]*(2*n+1)+[3],[1,3,3]+r)
            for key in ['open_zero','open_odd','open_even_step','open_even']:counts[key]+=1
    for m,n in itertools.product(range(5),repeat=2):
        for r in short:
            for h in(0,2):
                c=(0,[2]*(2*m)+[1]+[2]*(2*n+1)+[3],h,r)
                assert run(table,c,4*m+4*n+7)==front(0,[2]*(2*m)+[1]+[2]*(2*n+1),[2,3]+r)
                counts['wall_round']+=1
            assert run(table,front(0,[2]*(2*m)+[1]+[2]*(2*n+3),[2]+r),4*m+12*n+23)==front(0,[2]*(2*m+2)+[1]+[2]*(2*n+1)+[3],[2,3]+r)
            counts['open_round']+=1
        for k in range(5):
            assert run(table,qconf(m,n+1,k),8*m+16*n+34)==qconf(m+1,n,k+1)
            assert run(table,qconf(m,n,k),drain_cost(m,n))==qconf(m+n,0,k+n)
            counts['Q_pair']+=1;counts['drain']+=1
    for m,k in itertools.product(range(6),repeat=2):
        assert run(table,qconf(m,0,k),16*m+2*k+30)==mainconf(k+2,m);counts['Q_finish']+=1
    assert run(table,(0,[],0,[]),24)==mainconf(1,0)
    for m,n in itertools.product(range(8),repeat=2):
        assert run(table,mainconf(m,n),main_cost(m,n))==mainconf(*nextparams(m,n));counts['main_returns']+=1
    unsafe=run(table,(0,[2,1,3],0,[]),27)
    assert unsafe==(1,[2,2,2,1,2,3],0,[])
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,
        invariant='A0, blank right tail, nearest-first left word2^(2m) 1 2^(2n+1)3',
        return_map=dict(m_prime='n+2',n_prime='m+n'),main_cost=coefficients(main_cost),drain_cost=coefficients(drain_cost),
        rejected_parity_control=dict(initial_left=[2,1,3],steps=27,final_state='B',final_head=0,final_right=[]),
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Fibonacci-counter macros and complete returns replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Fibonacci-counter native controls passed; no proof credit.')
if __name__=='__main__':main()
