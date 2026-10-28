"""Finite exact S076 word-grammar controls; universal Coq proofs provide credit."""
import argparse,itertools,json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT;PREFIX=ROOT/'research/burn39-s076'
MACHINE='1LB2RB1RB2LB_2RB3RA1LA0LB'
TABLE=[5,11,7,9,11,14,4,1]
P=list(map(int,'110'));Q=list(map(int,'223'));G=list(map(int,'22323223132'));U=list(map(int,'1001010'))
BASERUNS=[[1,1,1,3],[4,1,3],[1,2,6],[5,6],[1,1,9],[4,9]]
PRE=[[1,2,1],[5,1],[1,1,4],[4,4]]
def word(g):
    t=g[0]
    rs=BASERUNS[t]if t<6 else PRE[t-6]+[2]*g[1]+runs(g[2])
    return list(map(int,'0'.join('1'*n for n in rs)))
def runs(g):return BASERUNS[g[0]]if g[0]<6 else PRE[g[0]-6]+[2]*g[1]+runs(g[2])
def nxt(g):
    t=g[0]
    if t<5:return(t+1,)
    if t==5:return(6,0,(0,))
    if t<9:return(t+1,g[1],g[2])
    return(6,g[1]+1,nxt(g[2]))
def normal(w):
    n=0
    while n<len(w)and w[n]==1:n+=1
    if n==len(w):
        assert n%2==1
        return n//2,[1],2*n+1
    assert n>0 and w[n]==0
    r=w[n+1:]
    if n%2:return n//2,[1]+r,2*n+1
    a,rr,c=normal(r)
    return n//2-1,[0]+[1,0]*a+[1,1]+rr,c+2*n+8+6*a

def trees(depth):
    gs=[(i,)for i in range(6)]
    for _ in range(depth):gs=[(i,)for i in range(6)]+[(i,m,g)for i in range(6,10)for m in range(3)for g in gs]
    return gs

def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def mainconf(n,g):return 0,[],0,U+P*n+word(g)
def cost(n,g):
    a,r,c=normal(word(g));return 12*n+65+c+6*a

def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[75]==MACHINE
    table=helper.codes(MACHINE);assert table==TABLE and sum(c*17**i for i,c in enumerate(table))==527732110
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['Q_train','read_gate','zero_gate','positive_train_gate','normalizers','grammar_successors','main_returns','actual_entry','actual_orbit','negative_guards','identity_controls']}
    for a in range(8):
        for l,r in itertools.product(contexts,repeat=2):
            assert run(table,back(1,Q+l,[2,1]*a+[0]+r),6*a+9)==back(1,l,[0,0]+[1,0]*a+[1,1]+r);counts['Q_train']+=1
    for n in range(8):
        for r in contexts:
            assert run(table,back(1,Q*n+G,[0]+r),9*n+31)==(0,[],0,U+P*(n+1)+[1,1]+r);counts['zero_gate']+=1
            assert run(table,(0,[],0,U+P*n+r),3*n+34)==front(1,Q*n+G,r);counts['read_gate']+=1
            if n:
                for a in range(8):
                    assert run(table,back(1,Q*n+G,[2,1]*a+[0]+r),9*n+6*a+31)==(0,[],0,U+P*(n+1)+[1,0]*a+[1,1]+r);counts['positive_train_gate']+=1
    gs=trees(2);assert len(gs)==942
    for g in gs:
        w=word(g);a,r,c=normal(w)
        assert word(nxt(g))==[1,0]*a+[1,1]+r;counts['grammar_successors']+=1
        for l in contexts:
            assert run(table,front(1,l,w),c)==back(1,l,[2,1]*a+[0]+r);counts['normalizers']+=1
        for n in range(1,5):
            assert cost(n,g)>0 and run(table,mainconf(n,g),cost(n,g))==mainconf(n+1,nxt(g));counts['main_returns']+=1
    assert run(table,(0,[],0,[]),234)==mainconf(1,(1,));counts['actual_entry']+=1
    elapsed=234;g=(1,)
    for n in range(1,33):elapsed+=cost(n,g);g=nxt(g)
    assert run(table,(0,[],0,[]),elapsed)==mainconf(33,g);counts['actual_orbit']+=1
    bad=run(table,(0,list(map(int,'3223132')),0,[]),51)
    assert bad[0]==1 and bad[2]==0 and not any(bad[3]);counts['negative_guards']+=1
    assert run(table,back(1,[],[0,1]),31)!=(0,[],0,U+P+[1,1,1]);counts['negative_guards']+=1
    wrong_A3='1LB2RB1RB2LA_2RB3RA1LA0LB';wrong_B3='1LB2RB1RB2LB_2RB3RA1LA0RB'
    for machine in(wrong_A3,wrong_B3):
        wrong=helper.codes(machine);assert wrong!=table
        assert run(wrong,mainconf(1,(1,)),cost(1,(1,)))!=mainconf(2,(2,));counts['identity_controls']+=1
    prior=PREFIX.with_name(PREFIX.name+'-prior-state-holdouts.txt');rows=prior.read_text().splitlines();assert len(rows)==5 and MACHINE in rows
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic controls only; no universal proof credit.',rows=[dict(machine=MACHINE,code=527732110)],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),prior_remaining_count=5,prior_remaining_report=str(prior.relative_to(ROOT)),prior_remaining_sha256=helper.sha(prior),
        grammar_tree_depth=2,grammar_trees=len(gs),wrapper_counter_range=[0,2],context_max_length=2,entry_steps=234,entry_prefix_count=1,entry_tree='G1',
        invariant='A0 at left blank; right1001010(110)^n word(g), n>0; six base words and four finite recursive wrappers',
        return_parameters='(n,g)->(n+1,next(g))',return_cost='12*n+65+c(g)+6*a(g); normalizer returns (21)^a0r in c steps',
        read_gate_cost=dict(slope=3,constant=34),Q_train_cost=dict(slope=6,constant=9),positive_gate_cost='9*n+6*a+31, n>0',
        actual_orbit=dict(returns=32,total_steps=elapsed),boundary_guard='Positive train gate requires n>0; unrestricted32/322 words with3132 tail are false.',
        identity_negative_controls=[wrong_A3,wrong_B3],source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S076 context scans, trains, recursive grammar and actual-entry controls replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S076 native controls passed:',counts)
if __name__=='__main__':main()
