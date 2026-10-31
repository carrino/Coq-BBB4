"""Finite exact-table S040 wall/scan controls; universal Coq proofs supply credit."""
import argparse,itertools,json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
PREFIX=ROOT/'research/burn27-s040-word-cycle'
MACHINE='1LB2LA3RA0RB_2RB2RA3LA1LB'
P=list(map(int,'332330202020332330'));E=list(map(int,'131133131313131133'));H=E[1:]+[1];V=P[1:]+[3]
F=[list(map(int,w))for w in ['22','203','20332','33233222','332330322','3323303303','3323302233022','33233020333022','332330202033032','3323302020223303','33233020202033303']]
K=[5,11,31,43,51,81,47,69,87,55,97]
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def stage(i,n,r):return 0,P*n+F[i],0,r
def mainconf(n):return stage(0,n,[])
def main_cost(n):return 1056*n+577
def gate_cost(q,n):return 30*n+(1 if q==1 else 3)
def phase_cost(i,n):return 96*n+K[i]
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def linear(f):return dict(slope=f(1)-f(0),constant=f(0))
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[39]==MACHINE
    table=helper.codes(MACHINE);assert table==[5,8,14,3,11,10,12,5]
    programs=PREFIX.with_name(PREFIX.name+'-programs.json');data=json.loads(programs.read_text())
    assert data['metadata_revision']==1 and data['machine']==MACHINE and data['word']==P and data['emitted']==E and data['right_block']==H and data['return_word']==V and data['walls']==F and data['phase_constants']==K
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['boundary_programs','left_scan','right_scan','B_gate','A_gate','rows','main_returns','actual_entry','negative_guards']}
    assert len(data['programs'])==11
    for i,row in enumerate(data['programs']):
        assert row['index']==i and row['wall']==F[i] and row['next_wall']==(F[i+1]if i<10 else P+F[0])
        assert row['steps']+(1 if row['state']==1 else 3)+1==K[i]
        for r in contexts:
            assert run(table,back(1,F[i],r),row['steps'])==front(row['state'],row['left'],r);counts['boundary_programs']+=1
    for n in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(1,P*n+l,r),66*n)==back(1,l,E*n+r);counts['left_scan']+=1
            assert run(table,(0,l,2,H*n+r),30*n)==(0,V*n+l,2,r);counts['right_scan']+=1
    for n in range(16):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,front(1,l,E*n+[1]+r),gate_cost(1,n))==front(0,P*n+[2]+l,r);counts['B_gate']+=1
            assert run(table,front(0,[2]+l,E*n+[1]+r),gate_cost(0,n))==front(0,P*n+[3,3]+l,r);counts['A_gate']+=1
        for i in range(11):
            nxt=F[i+1]if i<10 else P+F[0]
            for r in contexts:
                assert run(table,stage(i,n,r),phase_cost(i,n))==front(0,P*n+nxt,r);counts['rows']+=1
        assert sum(phase_cost(i,n)for i in range(11))==main_cost(n)
        assert run(table,mainconf(n),main_cost(n))==mainconf(n+1);counts['main_returns']+=1
    assert run(table,(0,[],0,[]),3)==mainconf(0);counts['actual_entry']+=1
    assert run(table,front(0,[0],[1]),3)!=front(0,[3,3],[]);counts['negative_guards']+=1
    assert run(table,front(1,[],[0]),1)!=front(0,[2],[]);counts['negative_guards']+=1
    wrong_A3='1LB2LA3RA0RA_2RB2RA3LA1LB';wrong_B3='1LB2LA3RA0RB_2RB2RA3LA1LA'
    for machine in(wrong_A3,wrong_B3):
        assert helper.codes(machine)!=table
        assert run(helper.codes(machine),mainconf(0),main_cost(0))!=mainconf(1);counts['negative_guards']+=1
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,invariant='A0, empty right, nearest-first left(332330202020332330)^n22; blank entry n0 at3',
        main_cost=linear(main_cost),B_gate_cost=linear(lambda n:gate_cost(1,n)),A_gate_cost=linear(lambda n:gate_cost(0,n)),phase_costs=[linear(lambda n,i=i:phase_cost(i,n))for i in range(11)],
        boundary_guard='A right gate requires left support2; both right gates require the terminal right tag1.',identity_negative_controls=[wrong_A3,wrong_B3],programs_report=str(programs.relative_to(ROOT)),programs_sha256=helper.sha(programs),
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S040 wall programs, scans and eleven-phase cycles replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S040 native controls passed; no proof credit.')
if __name__=='__main__':main()
