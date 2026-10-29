"""Finite controls for the frozen S009 run sibling; universal Coq lemmas supply proof credit."""
import argparse
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
REPORT=ROOT/'research/burn20-run-sibling-native.json'
MACHINE='1LB0LB1LA3RB_3RB3RA1RB2LB'
REJECTED_MACHINE='1LB0LB1LA3RA_3RB3RA1RB2LB'
def first_false_cost(n):return 16*n+16
def enc(ds):return[s for b in ds for s in([3,3]if b else[1,1])]
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def mainconf(ds,r):return 0,[3]+enc(ds)+[3],0,r

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
    assert REJECTED_MACHINE not in checkpoint.read_text().splitlines()
    table=helper.codes(MACHINE)
    rejected=helper.codes(REJECTED_MACHINE)
    assert table==[5,1,4,15,15,14,7,9] and table!=rejected
    expected=front(0,[3,3],[0])
    assert run(table,front(0,[3],[2,0]),3)==expected
    assert run(rejected,front(0,[3],[2,0]),3)!=expected
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    controls=dict(left_threes=0,right_B_twos=0,right_A_twos=0,first_false=0,overflow=0,complete_words=0)
    for n in range(9):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(1,[3]*n+l,r),n)==back(1,l,[2]*n+r)
            assert run(table,front(1,l,[2]*n+r),n)==front(1,[1]*n+l,r)
            assert run(table,front(0,[3]+l,[2]*n+r),3*n)==front(0,[3]*n+[3]+l,r)
            controls['left_threes']+=1;controls['right_B_twos']+=1;controls['right_A_twos']+=1
            assert run(table,(0,[3]*n+[1,1]+l,0,r),8*n+8)==(0,[3]*(n+2)+l,0,r)
            controls['first_false']+=1
        for pad in range(4):
            assert run(table,mainconf([True]*n,[0]*pad),4*n+7)==mainconf([False]*(n+1),[0]*max(0,pad-1))
            controls['overflow']+=1
    for size in range(9):
        for ds in itertools.product((False,True),repeat=size):
            if all(ds):out=[False]*(size+1);cost=4*size+7
            else:
                n=ds.index(False);out=list(ds);out[n]=True;cost=first_false_cost(n)
            assert run(table,mainconf(ds,[]),cost)==mainconf(out,[])
            controls['complete_words']+=1
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=2,scope='Finite synthetic controls only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],
        controls=controls,max_bits=8,max_run=8,context_max_length=2,
        rejected_target_control=dict(machine=REJECTED_MACHINE,codes=rejected,reason='A3=3RA is outside the frozen cohort and fails the supported three-step scan'),
        frozen_checkpoint_sha256=helper.sha(checkpoint),
        invariant='A0, blank right tail, nearest-first left word3 enc(bits)3; false=11,true=33',
        first_false=f'true^n false tail ->true^n true tail, cost{first_false_cost(1)-first_false_cost(0)}n+{first_false_cost(0)}',
        overflow='true^n ->false^(n+1), cost4n+7',
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Run-sibling macro and complete-word controls replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Run-sibling native controls passed; no proof credit.')
if __name__=='__main__':main()
