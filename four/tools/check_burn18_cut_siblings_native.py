"""Finite controls for the shared regular-cut macros; no proof credit."""
import argparse
import itertools
import json
import time
from pathlib import Path
import burn10_marker_history_pilot as helper

ROOT=helper.ROOT
REPORT=ROOT/'research/burn18-cut-siblings-native.json'
MACHINES=['1LB2LA0RA2LB_3RB1LA0RB3RA','1LB2LA1RA2LB_3RB1LA0RB3RA']

def run(table, conf, count):
    state,left,head,right=conf
    for _ in range(count):
        cell=table[4*state+head]
        write,direction,state=cell//4,cell//2%2,cell%2
        if direction:
            left=[write]+left
            head,right=(right[0]if right else 0),right[1:]
        else:
            right=[write]+right
            head,left=(left[0]if left else 0),left[1:]
    return state,left,head,right

def back(state,left,right):return state,left[1:],(left[0]if left else 0),right

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    start=time.monotonic()
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    checks=0
    for bit,machine in enumerate(MACHINES):
        table=helper.codes(machine)
        for left,right in itertools.product(contexts,repeat=2):
            assert run(table,back(1,[0]+left,[1]+right),3)==back(1,left,[2,1]+right)
            assert run(table,back(1,[3]+left,[1]+right),3)==back(1,left,[2,2]+right)
            checks+=2
            for n in range(8):
                assert run(table,back(1,[0]+left,[2]*(n+1)+[1]+right),n+4)==back(1,[0]*n+[3]+left,[1,1]+right)
                if bit:
                    assert run(table,back(1,[3]+left,[2]*n+[1]+right),2*n+3)==back(1,left,[2]*(n+2)+right)
                else:
                    assert run(table,back(1,[3]+left,[2]*(n+1)+[1]+right),n+4)==back(1,[0]*n+[3]+left,[1,2]+right)
                checks+=2
        assert run(table,(0,[],0,[]),1)==back(1,[],[1])
        assert run(table,back(1,[3],[1]),3)==back(1,[],[2,2])
        assert run(table,back(1,[],[2,2]),3)==(1,[0,0,3],0,[])
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=m,code=sum(v*17**i for i,v in enumerate(helper.codes(m))))for m in MACHINES],
        macro_checks=checks,context_max_length=2,max_twos=8,
        invariant='B cut: left/current in {0,3}, right in {1,2}, count(1,right)>count(3,left/current)',
        excluded_corner='Equal counts can return to B with a right suffix containing only twos, then drift into blanks.',
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        saved=json.loads(REPORT.read_text());assert all(saved[k]==v for k,v in stable.items())
        print('Regular-cut macro controls replayed exactly.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        helper.exact(REPORT,dict(stable,seconds=round(time.monotonic()-start,6)))
        print('Regular-cut macro controls passed; no proof credit.')
if __name__=='__main__':main()
