"""Finite exact-table S036 controls; universal Coq context proofs provide credit."""
import argparse,itertools,json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
PREFIX=ROOT/'research/burn31-s036'
MACHINE='1LB2LA2RB1RA_3RB3LA0LB0RB'
P=list(map(int,'2301'));Q=list(map(int,'1102'));E=list(map(int,'0123'))
U=list(map(int,'30130031022'));W=list(map(int,'30030031022300'))
C=[10,10,36,120,136,20,20,46,104,30,30,56,220]
OFF=[0,0,0,0,0,1,1,1,1,2,2,2,2]
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def boundary(n,r):return 0,[],0,P*n+r
def support(n):return Q*n+[1,1]
def mainconf(n,r):return boundary(n,U+r)
def main_cost(n):return 130*n+838
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[35]==MACHINE
    table=helper.codes(MACHINE);assert table==[5,8,11,6,15,12,1,3]
    assert sum(c*17**i for i,c in enumerate(table))==1273477485
    programs=PREFIX.with_name(PREFIX.name+'-programs.json');data=json.loads(programs.read_text())
    assert data['metadata_revision']==1 and data['machine']==MACHINE and data['table']==table and data['code']==1273477485 and data['frozen_row']==36
    assert data['word']=='2301'and data['left_support']=='1102'and data['emitted']=='0123'and data['wall']=='30130031022'and data['inserted']=='30030031022300'
    assert data['phase_constants']==C and data['offsets']==OFF and data['entry_steps']==2758 and data['entry_n']==8
    walls=[list(map(int,s))for s in data['walls']];assert len(walls)==13 and walls[0]==U and len(data['programs'])==8
    def phase(i,n,r):return boundary(n+OFF[i],walls[i]+r)
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['finite_programs','left_scan','right_scan','B_gate','A_gate','rows','phases','main_returns','actual_entry','negative_guards','identity_controls']}
    for row in data['programs']:
        u,v=list(map(int,row['input'])),list(map(int,row['emit']))
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,front(0,l,u+r),row['local'])==back(row['q'],l,v+r);counts['finite_programs']+=1
    for n in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,front(0,l,P*n+r),6*n)==front(0,Q*n+l,r);counts['right_scan']+=1
            assert run(table,back(1,Q*n+l,r),4*n)==back(1,l,E*n+r);counts['left_scan']+=1
    for n in range(16):
        for r in contexts:
            assert run(table,back(1,support(n),r),4*n+2)==boundary(n,[2,3]+r);counts['B_gate']+=1
            assert run(table,back(0,support(n),r),4*n+2)==boundary(n,[2,2]+r);counts['A_gate']+=1
    for n in range(12):
        for r in contexts:
            for row in data['programs']:
                u,v=list(map(int,row['input'])),list(map(int,row['emit']));tag=[2,2]if row['q']==0 else[2,3]
                assert run(table,boundary(n,u+r),10*n+row['local']+7)==boundary(n,tag+v+r);counts['rows']+=1
            for i in range(13):
                target=phase(i+1,n,r)if i<12 else mainconf(n+3,W+r)
                assert run(table,phase(i,n,r),10*n+C[i])==target;counts['phases']+=1
            assert sum(10*n+c for c in C)==main_cost(n)
            assert run(table,mainconf(n,r),main_cost(n))==mainconf(n+3,W+r);counts['main_returns']+=1
    assert run(table,(0,[],0,[]),2758)==mainconf(8,data['entry_suffix']);counts['actual_entry']+=1
    for q,tag in[(0,[2,2]),(1,[2,3])]:
        assert run(table,back(q,[],[3,2,1]),2)!=boundary(0,tag+[3,2,1]);counts['negative_guards']+=1
    wrong_A2='1LB2LA2RA1RA_3RB3LA0LB0RB';wrong_B1='1LB2LA2RB1RA_3RB3LB0LB0RB'
    for machine in(wrong_A2,wrong_B1):
        assert helper.codes(machine)!=table
        assert run(helper.codes(machine),mainconf(0,[]),main_cost(0))!=mainconf(3,W);counts['identity_controls']+=1
    prior=PREFIX.with_name(PREFIX.name+'-prior-state-holdouts.txt');assert len(prior.read_text().splitlines())==12 and MACHINE in prior.read_text().splitlines()
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',rows=[dict(machine=MACHINE,code=1273477485)],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),prior_remaining_count=12,prior_remaining_report=str(prior.relative_to(ROOT)),prior_remaining_sha256=helper.sha(prior),context_max_length=2,
        invariant='A0, empty left, right (2301)^n 30130031022 r; arbitrary suffix r; blank entry n8 at2758',
        main_cost=dict(slope=130,constant=838),return_parameters='(n,r) -> (n+3,30030031022300++r)',
        B_gate_cost=dict(slope=4,constant=2),A_gate_cost=dict(slope=4,constant=2),phase_costs=[dict(slope=10,constant=c)for c in C],
        boundary_guard='Both left gates require exact nearest-first left support(1102)^n11. The cycle never inspects its arbitrary right suffix.',
        identity_negative_controls=[wrong_A2,wrong_B1],programs_report=str(programs.relative_to(ROOT)),programs_sha256=helper.sha(programs),
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S036 finite programs, supported gates and thirteen-phase context cycles replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S036 native controls passed; no proof credit. Counts:',counts)
if __name__=='__main__':main()
