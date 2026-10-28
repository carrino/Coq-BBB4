"""Finite exact-table controls for frozen S050; universal Coq macros supply proof credit."""
import argparse
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
REPORT=ROOT/'research/burn20-paired-wall-counter-native.json'
MACHINE='1LB2LB1LA1RA_3RB3LA3LB0RB'
P=[3,0];W=[3,2,1,1];Q=[3,2]
def pairs(n):return P*n
def words(n):return W*n
def left(n):return pairs(n)+[0]
def stage(a,n,r):return 0,[1]*a+left(n),0,r
def X(n,r):return 0,[1]+left(n),1,r
def Y(n,r):return 0,[1,1]+left(n),1,r
def Z(n,r):return 0,[1,1,1]+left(n),1,r
def front(l,r):return 0,l,r[0]if r else 0,r[1:]
def mainconf(n):return stage(4,4*n+2,[])
def main_cost(n):return 416*n+577
def odd_cost(n):return 52*n+63
def even_cost(n):return 156*n+285
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def linear(f):return dict(slope=f(1)-f(0),constant=f(0))
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert MACHINE in checkpoint.read_text().splitlines()
    table=helper.codes(MACHINE);assert table==[5,9,4,6,15,12,13,3]
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['left20','guarded32','guarded58','guarded_odd_finish','guarded_even_finish1','guarded_even_finish2','odd_turn','even_turn','L_scan','R32_scan','R58_scan','four_phase','odd_phase','even_phase1','even_phase2','even_phase','main_returns']}
    for l,r in itertools.product(contexts,repeat=2):
        assert run(table,(0,[1]+P*2+l,1,r),20)==(0,[1]+l,1,W+r);counts['left20']+=1
        for h in(0,3):
            L=[h]+l
            assert run(table,(0,[1,1]+L,1,Q+W+r),32)==(0,[1,1]+P*2+L,1,Q+r)
            assert run(table,(0,[1,1]+L,1,Q+[1,1,1]+W+r),58)==(0,[1,1]+P*2+L,1,Q+[1,1,1]+r)
            assert run(table,(0,[1,1]+L,1,Q+[3,1]+r),23)==front([1,1,1]+P*2+L,r)
            assert run(table,(0,[1,1]+L,1,Q+[1,1,1,3,1]+r),57)==(0,[1,1,1]+P*2+L,1,Q+r)
            assert run(table,(0,[1,1]+L,1,Q+[1,1,1]+Q+Q+r),114)==front([1]*4+P*4+L,r)
            for key in ['guarded32','guarded58','guarded_odd_finish','guarded_even_finish1','guarded_even_finish2']:counts[key]+=1
    for r in contexts:
        assert run(table,X(1,r),38)==Y(0,Q+r);counts['odd_turn']+=1
        assert run(table,X(0,W+r),35)==Y(0,Q+[1,1,1]+r);counts['even_turn']+=1
    for n,p in itertools.product(range(8),repeat=2):
        for r in contexts:
            assert run(table,X(2*n+p,r),20*n)==X(p,words(n)+r)
            assert run(table,Y(p,Q+words(n)+r),32*n)==Y(p+2*n,Q+r)
            assert run(table,Y(p,Q+[1,1,1]+words(n)+r),58*n)==Y(p+2*n,Q+[1,1,1]+r)
            for key in ['L_scan','R32_scan','R58_scan']:counts[key]+=1
    for n in range(8):
        for r in contexts:
            assert run(table,stage(4,n,r),21)==front([1]*3+left(n+1),r);counts['four_phase']+=1
            assert run(table,stage(3,2*n+1,r),odd_cost(n))==front([1]*3+left(2*n+2),r);counts['odd_phase']+=1
            assert run(table,stage(3,2*(n+1),r),78*n+114)==Z(2*(n+1),Q+r);counts['even_phase1']+=1
            assert run(table,Z(2*(n+1),Q+r),78*n+171)==front([1]*4+left(2*n+4),r);counts['even_phase2']+=1
            assert run(table,stage(3,2*(n+1),r),even_cost(n))==front([1]*4+left(2*n+4),r);counts['even_phase']+=1
    assert run(table,(0,[],0,[]),149)==mainconf(0)
    for n in range(16):
        assert run(table,mainconf(n),main_cost(n))==mainconf(n+1);counts['main_returns']+=1
    assert run(table,(0,[1,1,1],1,Q+W),32)!=(0,[1,1]+P*2+[1],1,Q)
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,
        invariant='A0, blank right tail, nearest-first left word1^4 (30)^(4n+2)0',
        main_cost=linear(main_cost),odd_phase_cost=linear(odd_cost),positive_even_phase_cost=linear(even_cost),
        boundary_guard='after the left11 prefix, the wall head is0 or3; arbitrary1 invalidates the right32 macro',
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Paired-wall counter macros and complete returns replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Paired-wall counter native controls passed; no proof credit.')
if __name__=='__main__':main()
