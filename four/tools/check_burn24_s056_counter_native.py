"""Bounded S056 three-phase reset controls; native computations confer no proof credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB1RA3RA_3RB3LA2RB2LB'
TABLE=codes(MACHINE)
def run(c,n):
    q,l,h,r=c;l,r=list(l),list(r)
    for _ in range(n):
        v=TABLE[4*q+h];q=v&1;x=v//4
        if v&2:l=[x]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[x]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r
def front(q,l,r):return q,list(l),(r[0]if r else 0),list(r[1:])
def P(k):return [1,1,3]*k
def X(k,b,l):return P(k)+[3]+P(k)+[1]+[2]*b+list(l)
def Y(k,b,l):return P(k)+[1,3,3]+P(k)+[1]+[2]*b+list(l)
def Z(k,b,l):return P(k)+[1,1,1,1,3]+P(k)+[1]+[2]*b+list(l)
def G(m):return 0,[3,1]+[2]*m+[3],0,[]
def tin(ts):return [x for b in ts for x in([1,1]if b else[3])]
def check():
    assert TABLE==[5,9,6,14,15,12,11,9]
    ctx=[[]]+[[x]for x in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    phases=stops=fallbacks=caps=resets=0
    for k,b,l,r in itertools.product(range(9),range(8),ctx,ctx):
        for src,dst,dt in[(X,Y,11),(Y,Z,15),(Z,lambda k,b,l:X(k+1,b,l),21)]:
            assert run((0,src(k,b+1,l),0,r),18*k+dt)==front(0,dst(k,b,l),r);phases+=1
    for k,x,l,r in itertools.product(range(9),[2,3],ctx,ctx):
        y=1 if x==2 else 3
        a=P(k)+[3]+P(k)+[1,x]+l
        b=P(k)+[1,3,3]+P(k)+[1,x]+l
        c=P(k)+[1,1,1,1,3]+P(k)+[1,x]+l
        assert run((0,a,0,r),18*k+11)==front(0,P(k)+[1,3,3]+P(k)+[y]+l,r)
        assert run((0,b,0,r),18*k+15)==front(0,P(k)+[1,1,1,1,3]+P(k)+[y]+l,r)
        assert run((0,c,0,r),18*k+21)==front(0,P(k+1)+[3]+P(k+1)+[y]+l,r);stops+=3
    for n in range(1,9):
        for ts in itertools.product([False,True],repeat=n):
            w=tin(ts);assert run((0,w,0,[]),2*len(w)+2*sum(ts)+5)==G(len(w)-1);fallbacks+=1
    for k in range(100):
        for b,cost,m1 in[(1,52*k+47,6*k+5),(2,70*k+72,6*k+7)]:
            assert run((0,X(k,b,[3]),0,[]),cost)==G(m1);caps+=1
    drift=[]
    for m in range(65):
        if m%3:
            cost=3*(m+3)**2-(1 if m%3==1 else 3)
            assert run(G(m),cost)==G(2*m+3);resets+=1
        else:
            cost=3*m*m+20*m+26;c=run(G(m),cost)
            assert c[0]==1 and c[2]==0 and not c[3];drift.append(dict(m=m,first_B0_blank=cost))
    assert run((0,[],0,[]),14)==G(1)
    assert run((0,[1,3],0,[]),10)==(1,[2,2,3],2,[])
    # Match the reset trajectory in a single direct blank simulation.
    m=1;t=14;targets={t:m}
    while True:
        t+=3*(m+3)**2-(1 if m%3==1 else 3);m=2*m+3
        if t>2000000:next_reset=dict(time=t,m=m);break
        targets[t]=m
    q=p=0;d={};lo=0;hi=-1
    for t in range(2000001):
        if t in targets:
            m=targets[t]
            assert q==0 and d.get(p,0)==0 and p>hi
            assert [d.get(x,0)for x in range(p-1,lo-1,-1)]==[3,1]+[2]*m+[3]
        c=TABLE[4*q+d.get(p,0)];d[p]=c//4;lo=min(lo,p);hi=max(hi,p);p+=1 if c&2 else-1;q=c&1
    return dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(TABLE)),state_bound=0,
                arbitrary_context_phase_controls=phases,general_stop_context_controls=stops,
                all_token_fallback_controls=fallbacks,residue_cap_controls=caps,reset_controls=resets,
                actual_entry_steps=14,direct_blank_steps=2000000,
                direct_resets=[dict(time=t,m=m)for t,m in targets.items()],next_reset_prediction=next_reset,
                reset_formula='m mod3 nonzero -> G(2m+3), cost3(m+3)^2-1 for residue1 / -3 for residue2',
                excluded_divisible_reset_seeds=drift,negative_controls=['arbitrary left13 escapes to B2 at10','every tested m divisible3 escapes to B0'])
def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn24-s056-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps({k:v for k,v in row.items()if k not in['direct_resets','excluded_divisible_reset_seeds']}),flush=True)
if __name__=='__main__':main_cli()
