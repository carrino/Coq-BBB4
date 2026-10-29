"""Finite exact-table controls for frozen S010; universal Coq gates supply proof credit."""
import argparse,itertools,json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
PREFIX=ROOT/'research/burn26-s010-crossing'
MACHINE='1LB0LB1RB2LA_3RB3RA1RA0LA'
P=[3,3,1,1,3,3,1];E=[0,2,2,0,1,2,0];V=[1,3,3,1,1,3,3]
F=[[],[3,3,1],[3],[3,3,3,3,3,1],[3,3,1,1,1,1,3,3,1],[3,3,3,1,1,1],[1,1,3,3,3,3,1],[1,1,1,3,3,1],[3,3,3,1]]
PADDING=[5,4,3,2,1,0,1,4,6]
PHASES=[(1,0,16,9),(2,1,32,33),(3,0,32,25),(4,0,16,21),(5,2,80,165),(6,4,240,707),(7,0,16,21),(8,0,0,6),(0,1,16,17)]
def tail(n):return P*n+[3,3]
def phase(i,n,r):return 0,F[i]+tail(n),0,[0]*PADDING[i]+r
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def main_cost(n):return 448*n+2076
def gate_cost(q,n):return 16*n+(7 if q==0 else 6)
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def instantiate(c,l,r):
    q,L,h,R=c
    assert L[-1]=='T'and R[-1]=='r'
    return q,L[:-1]+l,h,R[:-1]+r
def linear(f):return dict(slope=f(1)-f(0),constant=f(0))
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[9]==MACHINE
    table=helper.codes(MACHINE);assert table==[5,1,7,8,15,14,6,0]
    programs=PREFIX.with_name(PREFIX.name+'-programs.json');data=json.loads(programs.read_text())
    assert data['metadata_revision']==1 and data['machine']==MACHINE and data['word']==P and data['prefixes']==F and data['right_padding']==PADDING
    assert data['phases']==[dict(destination=j,word_add=d,slope=s,constant=c)for j,d,s,c in PHASES]
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['finite_context_programs','left_scan','right_scan','B_gate','A_gate','phases','cycles','actual_entry','negative_guards']}
    for chunks in data['programs']:
        for chunk in chunks:
            for l,r in itertools.product(contexts,repeat=2):
                if'gate_state'in chunk:
                    assert chunk['right'][-1]=='r'
                    expected=back(chunk['gate_state'],l,chunk['right'][:-1]+r)
                else:expected=instantiate(chunk['finish'],l,r)
                assert run(table,instantiate(chunk['start'],l,r),chunk['steps'])==expected;counts['finite_context_programs']+=1
    for n in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(1,P*n+l,r),9*n)==back(1,l,E*n+r);counts['left_scan']+=1
            assert run(table,(1,l,0,E*n+r),7*n)==(1,V*n+l,0,r);counts['right_scan']+=1
    for n in range(16):
        for r in contexts:
            assert run(table,back(1,tail(n),r),gate_cost(1,n))==(1,[1]+tail(n),0,r);counts['B_gate']+=1
            assert run(table,back(0,tail(n),r),gate_cost(0,n))==front(0,[1,1]+tail(n),r);counts['A_gate']+=1
            for i,(j,d,s,c)in enumerate(PHASES):
                assert run(table,phase(i,n,r),s*n+c)==phase(j,n+d,r);counts['phases']+=1
            assert run(table,phase(0,n,r),main_cost(n))==phase(0,n+8,r);counts['cycles']+=1
            m=n;cost=0
            for j,d,s,c in PHASES:cost+=s*m+c;m+=d
            assert m==n+8 and cost==main_cost(n)
    assert run(table,(0,[],0,[]),2079)==phase(0,8,[]);counts['actual_entry']+=1
    assert run(table,back(1,[],[]),6)!=(1,[1],0,[]);counts['negative_guards']+=1
    wrong_A3='1LB0LB1RB2LB_3RB3RA1RA0LA';wrong_B3='1LB0LB1RB2LA_3RB3RA1RA0LB'
    for machine in(wrong_A3,wrong_B3):
        assert helper.codes(machine)!=table
        assert run(helper.codes(machine),(0,[],0,[]),2079)!=phase(0,8,[]);counts['negative_guards']+=1
    gate_counts=[sum('gate_state'in c for c in chunks)for chunks in data['programs']]
    assert gate_counts==[1,2,2,1,5,15,1,0,1]
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(table)))],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),context_max_length=2,
        invariant='A0 with left(3311331)^n33 and right0^5; selected blank entry n8 at2079',
        main_cost=linear(main_cost),B_gate_cost=linear(lambda n:gate_cost(1,n)),A_gate_cost=linear(lambda n:gate_cost(0,n)),
        phase_costs=[dict(destination=j,word_add=d,**linear(lambda n,s=s,c=c:s*n+c))for j,d,s,c in PHASES],phase_gate_counts=gate_counts,
        boundary_guard='Finite left terminal33; explicit right blank padding tracks the nine physical head positions.',
        identity_negative_controls=[wrong_A3,wrong_B3],programs_report=str(programs.relative_to(ROOT)),programs_sha256=helper.sha(programs),
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S010 gates, finite contexts and nine-phase cycles replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S010 native controls passed; no proof credit.')
if __name__=='__main__':main()
