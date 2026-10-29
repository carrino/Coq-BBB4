"""Finite exact-table controls for frozen S075; universal Coq macros supply proof credit."""
import argparse
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
REPORT=ROOT/'research/burn20-pair-accumulator-native.json'
MACHINE='1LB2RB0LA2RA_1RB3LB2LB2RA'
def P(n):return[1,2]*n
def Q(n):return[3,2]*n
def R(n):return[2,3]*n
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def stage(a,b,r):return 0,[2]*a+[1]+P(b),0,r
def G(p,q,k):return front(0,[2,1]+P(p),[3]*(q+1)+[2]*k+[1])
def mainconf(a,b):return stage(a+1,b+1,[])
def main_cost(a,b):return 6*a*a+40*a+8*(a+2)*b+51
def physical_cost(a,b):return 6*a*a+20*a+9+8*(a+1)*b
def increment_cost(p,q):return 8*p+4*q+24
def finish_cost(p,q):return 8*p+5*q+27
def start_cost(a,p):return a+8*p+7
def restore_cost(p):return 8*p+5
def drain_cost(k,p,q):
    if k==0:return finish_cost(p,q)
    return increment_cost(p,q)+drain_cost(k-1,p+1,q+1)
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def linear(f):return dict(slope=f(1)-f(0),constant=f(0))
def affine2(f):return dict(first=f(1,0)-f(0,0),second=f(0,1)-f(0,0),constant=f(0,0))
def quadratic2(f):
    c=f(0,0);aa=(f(2,0)-2*f(1,0)+c)//2;bb=(f(0,2)-2*f(0,1)+c)//2
    return dict(first_squared=aa,second_squared=bb,first=f(1,0)-c-aa,second=f(0,1)-c-bb,
                mixed=f(1,1)-f(1,0)-f(0,1)+c,constant=c)
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert MACHINE in checkpoint.read_text().splitlines()
    table=helper.codes(MACHINE);assert table==[5,11,0,10,7,13,9,10]
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['support','A3_scan','B0_scan','A2_scan','B1_scan','B2_scan','B_pair_scan','restore','erase','start','increment_tag1','increment_tag2','loop','finish','drain','main_returns','negative_guards','actual_entry']}
    for l,r in itertools.product(contexts,repeat=2):
        assert run(table,front(0,[2,1]+l,[2,3]+r),6)==front(0,[2,1,1,2]+l,r);counts['support']+=1
        for n in range(6):
            assert run(table,front(0,l,[3]*n+r),n)==front(0,[2]*n+l,r);counts['A3_scan']+=1
            assert run(table,front(1,l,[0]*n+r),n)==front(1,[1]*n+l,r);counts['B0_scan']+=1
            assert run(table,back(0,[2]*n+l,r),n)==back(0,l,[0]*n+r);counts['A2_scan']+=1
            assert run(table,back(1,[1]*n+l,r),n)==back(1,l,[3]*n+r);counts['B1_scan']+=1
            assert run(table,back(1,[2]*n+l,r),n)==back(1,l,[2]*n+r);counts['B2_scan']+=1
            assert run(table,back(1,P(n)+l,r),2*n)==back(1,l,R(n)+r);counts['B_pair_scan']+=1
            assert run(table,front(0,[2]*n+[1]+l,[2]+r),2*n+3)==front(1,[1]*(n+1)+[2]+l,r);counts['erase']+=1
    for p in range(1,7):
        for r in contexts:
            assert run(table,back(1,P(p),r),restore_cost(p))==front(0,[2,1]+P(p),r);counts['restore']+=1
            for a in range(7):
                assert run(table,stage(a,p,r),start_cost(a,p))==front(0,[2,1]+P(p),[3]+[2]*a+[1]+r);counts['start']+=1
            for q in range(7):
                for tag in(1,2):
                    assert run(table,front(0,[2,1]+P(p),[3]*(q+1)+[2,tag]+r),increment_cost(p,q))==front(0,[2,1]+P(p+1),[3]*(q+2)+[3 if tag==1 else 2]+r)
                    counts['increment_tag'+str(tag)]+=1
    for p,q in itertools.product(range(1,6),range(5)):
        assert run(table,G(p,q,1),finish_cost(p,q))==stage(q+4,p+1,[]);counts['finish']+=1
        for k in range(6):
            assert drain_cost(k,p,q)==6*k*k+31*k+8*(k+1)*p+(4*k+5)*q+27
            assert run(table,G(p,q,k+1),drain_cost(k,p,q))==stage(q+k+4,p+k+1,[]);counts['drain']+=1
            if k:
                assert run(table,G(p,q,k+1),increment_cost(p,q))==G(p+1,q+1,k);counts['loop']+=1
    for a,b in itertools.product(range(8),repeat=2):
        assert main_cost(a,b)==physical_cost(a+1,b+1)==start_cost(a+1,b+1)+drain_cost(a,b+1,0)
        assert run(table,mainconf(a,b),main_cost(a,b))==mainconf(a+3,a+b+1);counts['main_returns']+=1
    assert run(table,(0,[],0,[]),68)==mainconf(3,1);counts['actual_entry']+=1
    assert run(table,stage(0,1,[]),physical_cost(0,1))!=stage(3,1,[]);counts['negative_guards']+=1
    assert run(table,back(1,[],[]),5)!=front(0,[2,1],[]);counts['negative_guards']+=1
    wrong_A3='1LB2RB0LA2RB_1RB3LB2LB2RA';wrong_B1='1LB2RB0LA2RA_1RB3LA2LB2RA'
    for machine in(wrong_A3,wrong_B1):
        assert machine!=MACHINE and helper.codes(machine)!=table
        assert run(helper.codes(machine),(0,[],0,[]),68)!=mainconf(3,1);counts['negative_guards']+=1
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,
        invariant='A0, blank right tail, nearest-first left word2^(a+1)1(12)^(b+1), a,b natural',
        main_return=dict(first_add=3,second='a+b+1'),physical_return=dict(first_add=3,second='a+b'),
        main_cost=quadratic2(main_cost),physical_cost=quadratic2(physical_cost),
        increment_cost=affine2(increment_cost),finish_cost=affine2(finish_cost),start_cost=affine2(start_cost),restore_cost=linear(restore_cost),
        boundary_guard='Both physical block lengths are positive; restoration requires a nonempty pair word.',
        identity_negative_controls=[wrong_A3,wrong_B1],
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Pair-accumulator scans, tags, drain, and returns replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Pair-accumulator native controls passed; no proof credit.')
if __name__=='__main__':main()
