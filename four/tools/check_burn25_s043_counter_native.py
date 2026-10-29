"""Bounded S043 sweep and stable-tail controls; no kernel proof credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LA3RB2LA_2RB2LA3RA0LB'
TABLE=codes(MACHINE)
def run(c,n):
    q,l,h,r=c;l,r=list(l),list(r)
    for _ in range(n):
        v=TABLE[4*q+h];q=v&1;x=v//4
        if v&2:l=[x]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[x]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r
def front(q,l,r):return q,list(l),(r[0]if r else 0),list(r[1:])
def back(q,l,r):return q,list(l[1:]),(l[0]if l else 0),list(r)
def left(a,r):return 0,[],0,[2]*a+list(r)
def C(a,b):return left(a,[1]*b+[0,1])
def M(n):return C(5,2*n)
def check():
    assert TABLE==[5,8,15,8,11,8,14,1]
    ctx=[[]]+[[x]for x in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    sweeps=consumes=drains=0
    for n,l,r in itertools.product(range(9),ctx,ctx):
        assert run(back(0,[3]*n+l,r),n)==back(0,l,[2]*n+r)
        assert run(back(1,[3]*n+l,r),n)==back(1,l,[0]*n+r)
        assert run(front(1,l,[0]*n+r),n)==front(1,[2]*n+l,r)
        assert run(back(1,[2]*n+l,[0]+r),3*n)==back(1,l,[0]+[1]*n+r)
        assert run(front(0,l,[2]*(2*n+1)+r),2*n+1)==front(1,[3]*(2*n+1)+l,r);sweeps+=5
        for q in range(2):
            assert run(front(q,l,[2]*n+[1]+r),n+1)==back(0,[3]*n+l,[2]+r)
            assert run(front(q,l,[2]*(2*n)+r),2*n)==front(q,[3]*(2*n)+l,r);sweeps+=2
    for r in ctx:
        assert run(left(0,r),5)==front(0,[3,3],r)
        assert run(back(1,[],[0,1,1,1]+r),17)==left(5,r);sweeps+=2
    for a,r in itertools.product(range(25),ctx):
        assert run(left(a,[1]+r),2*a+8)==left(a+3,r);consumes+=1
    for a,b,r in itertools.product(range(13),range(13),ctx):
        assert run(left(a,[1]*b+r),3*b*b+(2*a+5)*b)==left(a+3*b,r);drains+=1
    for n in range(101):
        assert run((0,[3]*n,0,[]),2*n+5)==(0,[3,3]+[2]*n,0,[])
        assert run((0,[3]*(n+3),0,[]),5*n+40)==C(5,n)
        assert run(C(2*n+1,0),12*n+60)==C(5,2*n+2)
    for n in range(33):assert run(M(n),12*n*n+66*n+84)==M(3*n+3)
    assert run(left(5,[]),10)==(1,[3]*7,0,[])
    assert run(C(5,1),112)==left(5,[1]*6+[0,0,0,1])
    assert run(C(2,0),58)==left(5,[0,0,0,1])
    assert run((0,[],0,[]),100852)==M(254)
    targets={100852:254,891892:765};q=p=0;d={};lo=0;hi=-1
    for t in range(1000001):
        if t in targets:
            n=targets[t]
            assert q==0 and d.get(p,0)==0 and p<lo
            assert [d.get(x,0)for x in range(p+1,hi+1)]==[2]*5+[1]*(2*n)+[0,1]
        v=TABLE[4*q+d.get(p,0)];x=v//4
        if x:d[p]=x;lo=min(lo,p);hi=max(hi,p)
        elif p in d:
            del d[p]
            if p==lo:lo=min(d,default=p)
            if p==hi:hi=max(d,default=p)
        p+=1 if v&2 else-1;q=v&1
    return dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(TABLE)),state_bound=0,
                arbitrary_context_sweeps=sweeps,consume_one_controls=consumes,drain_controls=drains,
                all_three_first_controls=101,all_three_final_controls=101,odd_reset_controls=101,
                stable_even_run_controls=33,actual_entry_steps=100852,actual_entry_parameter=254,
                direct_blank_steps=1000000,direct_stable_cuts=[dict(time=t,n=n)for t,n in targets.items()],
                next_stable_cut_prediction=dict(time=7965166,n=2298),
                stable_return='M(n)=A0 empty-left/right2^5 1^(2n)01 -> M(3n+3), cost12n^2+66n+84',
                negative_controls=['missing01 tail reaches B0 right blank at10','odd one-run changes tail01 to0001','even reset two-run changes tail01 to0001'])
def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn25-s043-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps(row),flush=True)
if __name__=='__main__':main_cli()
