"""Independent finite sweep, phase, orbit and negative controls for S004/S005; zero credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT/'research/burn23-s004-s005-unary'
MACHINES = ('1LB0LA1LB1RB_3RB3RA0RB2LA', '1LB0LA1LB1RB_3RB3RA2RB2LA')
P = [0,2,1,0,0,2,1,2,1]
R = [0,0,2,1,2,1,0,2,1]
TAILS = ([], [0,2,1,2,1], [0,2,1,0,2,1,2,1], [0,2,1,0,0,2,1,0,0,2,1,2,1])
TERMINAL_RIGHTS = ([2,1], [0,2,1,2,1], [0,0,2,1,0,0,2,1,2,1], [0,0,2,1,2,1,0,2,1,0,0,2,1,2,1])
TERMINAL_COSTS = (16,24,64,100)
PHASE_COSTS = (22,30,70,106)
def artifact(s):return PREFIX.with_name(PREFIX.name+'-'+s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def step(table,conf):
    q,left,head,right=conf;value=table[4*q+head];assert value!=16
    write,direction,q=value//4,bool(value&2),value%2
    return ((q,[write,*left],right[0]if right else 0,right[1:])if direction
            else(q,left[1:],left[0]if left else 0,[write,*right]))
def steps(table,count,conf):
    for _ in range(count):conf=step(table,conf)
    return conf
def front(q,left,right):return q,left,right[0]if right else 0,right[1:]
def maincut(n,phase):return 1,[],0,[1]+P*n+TAILS[phase]
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    inp=artifact('native-input.json');data_in=json.loads(inp.read_text());assert data_in['machines']==list(MACHINES)
    frontier=ROOT/data_in['frontier_source'];assert sha(frontier)==data_in['frontier_sha256']
    assert set(MACHINES)<=set(frontier.read_text().splitlines())
    contexts=[list(w)for n in range(data_in['context_maximum_length']+1)for w in itertools.product(range(4),repeat=n)]
    sweep_controls=terminal_controls=phase_controls=cycle_controls=negative_controls=0
    tables=[codes(m)for m in MACHINES];macro_digests=[]
    for bit,table in enumerate(tables):
        x=2 if bit else 0;Q=[1,x,3,1,3,1,x,3,1]
        observations=[]
        for left,right in itertools.product(contexts,repeat=2):
            a=steps(table,41,front(0,[3,3]+left,P+right));assert a==front(0,[3,3]+Q+left,right)
            b=steps(table,17,(0,[3,1]+Q+left,x,right));assert b==(0,[3,1]+left,x,R+right)
            sweep_controls+=2
        for phase,left in itertools.product(range(4),contexts):
            out=steps(table,TERMINAL_COSTS[phase],front(0,[3,3]+left,TAILS[phase]))
            assert out==(0,[3,1]+left,x,TERMINAL_RIGHTS[phase]);terminal_controls+=1
        for n in range(data_in['maximum_block_count']+1):
            for phase in range(4):
                count=58*n+PHASE_COSTS[phase];out=steps(table,count,maincut(n,phase))
                expected=maincut(n,phase+1)if phase<3 else maincut(n+2,0)
                assert out==expected;phase_controls+=1
                observations.append(dict(blocks=n,phase=phase,steps=count,right_sha256=hashlib.sha256(bytes(out[3])).hexdigest()))
            assert steps(table,232*n+228,maincut(n,0))==maincut(n+2,0);cycle_controls+=1
        assert steps(table,9,(1,[],0,[1,2,1]))==(1,[1,x,1],0,[]);negative_controls+=1
        assert steps(table,47,(1,[],0,[1,2,1,2,1,2,1]))==(1,[1,3,1,x,3,1,1],0,[]);negative_controls+=1
        for left in ([],[1],[3,0,2]):
            conf=(1,left,0,[])
            for n in range(17):
                assert conf==(1,[3]*n+left,0,[]);conf=step(table,conf)
            negative_controls+=1
        assert steps(table,22,maincut(0,0))!=maincut(1,0);negative_controls+=1
        macro_digests.append(hashlib.sha256(json.dumps(observations,sort_keys=True).encode()).hexdigest())
    confs=[(0,[],0,[]),(0,[],0,[])];positions=[0,0];visits=[0,0]
    for _ in range(data_in['actual_blank_steps']):
        assert confs[0][0]==confs[1][0]and positions[0]==positions[1]
        visits[confs[0][0]]+=1
        for i,table in enumerate(tables):
            value=table[4*confs[i][0]+confs[i][2]];positions[i]+=1 if value&2 else -1
            confs[i]=step(table,confs[i])
    rows=[dict(machine=m,code=sum(v*17**i for i,v in enumerate(table)))for m,table in zip(MACHINES,tables)]
    sources=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope='Finite native macro and boundary controls only; zero proof credit.',rows=rows,
              block=P,backward_block=R,terminal_phases=list(TAILS),sweep_controls=sweep_controls,
              terminal_controls=terminal_controls,phase_controls=phase_controls,cycle_controls=cycle_controls,
              negative_boundary_controls=negative_controls,actual_blank_steps=data_in['actual_blank_steps'],
              identical_actual_state_position_trajectories=True,actual_state_visits=visits,
              phase_observation_sha256=macro_digests,
              inputs_sha256={str(p.relative_to(ROOT)):sha(p)for p in(inp,frontier)},
              source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources},
              checked_state_families=0,checked_instruction_families=0)
    report=artifact('native.json')
    if args.check:assert json.loads(report.read_text())==data
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:data[k]for k in('sweep_controls','terminal_controls','phase_controls','cycle_controls','negative_boundary_controls')}),flush=True)
if __name__=='__main__':main()
