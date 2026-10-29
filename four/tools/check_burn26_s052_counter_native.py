"""Bounded S052 recursive normalizer and six-phase controls; no kernel credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB1RA2LA_0RB3LB3RB1RA'
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
def F(a,b,r):return front(0,[1]*a+[3]*b+[0],r)
def H(n,r):return F(2*n+1,2,[3]+r)
def main(a,b):return 0,[1]*a+[3]*b+[0],0,[]
def M(k):return main(2,6*k+4)
def badcost(k):return 113*3**k-60*k-97
def acost(k):return 113*3**k-54*k-80
def bcost(k):return 226*3**k-72*k-133
def tcost(k):return 226*3**k-78*k-226
def check():
    assert TABLE==[5,9,6,8,3,13,15,6]
    ctx=[[]]+[[x]for x in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    sweeps=pair=local=families=phases=mainreturns=0
    for n,l,r in itertools.product(range(7),ctx,ctx):
        assert run(front(1,l,[2]*n+r),n)==front(1,[3]*n+l,r)
        assert run(front(0,l,[2]*n+r),n)==front(0,[1]*n+l,r)
        assert run(back(1,[1]*n+l,r),n)==back(1,l,[3]*n+r)
        assert run(back(0,[3]*n+l,r),n)==back(0,l,[2]*n+r);sweeps+=4
        assert run(back(1,[3]*(2*n)+l,[3,3]+r),10*n)==back(1,l,[3,3]+[2]*(2*n)+r);pair+=1
    for j,r in itertools.product(range(7),ctx):
        assert run(F(5,2*j,[3]+r),12*j+21)==F(5,2*j+1,r)
        assert run(F(5,2*j+1,[3]+r),12*j+13)==H(j,[3,2,2]+r)
        assert run(F(1,2*j,[3,3]+r),12*j+6)==F(2*j+1,2,r)
        assert run(F(3,2*j+2,[3,3]+r),12*j+26)==F(1,2*j+6,r);local+=4
    for k,r in itertools.product(range(5),ctx):
        assert run(H(3*k+1,r),badcost(k))==F(1,0,[3]+[2]*(6*k+4)+r)
        assert run(H(3*k+2,r),acost(k))==F(5,6*k+3,r)
        assert run(H(3*k+3,r),bcost(k))==F(7,6*k+3,r)
        assert run(F(5,3,[3]*(6*k)+r),tcost(k))==F(5,6*k+3,r);families+=4
    for k in range(6):
        p=3**k;B=6*k+4
        rows=[(2,B,3,B,36*k+41),(3,B,4,B,36*k+45),
              (4,B,6,B-1,113*p+18*k-2),(6,B-1,4,B+2,452*p-72*k-213),
              (4,B+2,8,B-1,226*p-31),(8,B-1,2,B+6,791*p-90*k-308)]
        for a,b,A,c,t in rows:assert run(main(a,b),t)==main(A,c);phases+=1
        assert run(M(k),1582*p-72*k-468)==M(k+1);mainreturns+=1
    for a,b,t in [(1,5,57),(4,2,79)]:
        q,l,h,r=run(main(a,b),t);assert q==1 and h==0 and r==[]
    assert run((0,[],0,[]),142)==M(0)
    # One unaccelerated blank run checks the recurrence against actual cuts.
    t=142;k=0;targets={t:k}
    while True:
        t+=1582*3**k-72*k-468;k+=1
        if t>2000000:prediction=dict(time=t,k=k);break
        targets[t]=k
    d={};q=p=0;lo=0;hi=-1
    for t in range(2000001):
        if t in targets:
            k=targets[t];assert q==0 and d.get(p,0)==0 and p>hi
            assert [d.get(x,0)for x in range(p-1,lo-1,-1)]==[1,1]+[3]*(6*k+4)
        v=TABLE[4*q+d.get(p,0)];x=v//4
        if x:d[p]=x;lo=min(lo,p);hi=max(hi,p)
        elif p in d:
            del d[p]
            if p==lo:lo=min(d,default=p)
            if p==hi:hi=max(d,default=p)
        p+=1 if v&2 else-1;q=v&1
    return dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(TABLE)),state_bound=0,
                arbitrary_context_sweeps=sweeps,pair_controls=pair,local_conversion_controls=local,
                recursive_family_context_controls=families,six_phase_controls=phases,whole_cycle_controls=mainreturns,
                actual_entry_steps=142,direct_blank_steps=2000000,direct_main_cuts=[dict(time=t,k=k)for t,k in targets.items()],
                next_cut_prediction=prediction,native_runtime_formula='1582*3^k-72k-468; native provenance only, not required by universal existential return proof.',
                negative_controls=['synthetic(a,b)=(1,5) escapes B0 at57','synthetic(a,b)=(4,2) escapes B0 at79'])
def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn26-s052-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps(row),flush=True)
if __name__=='__main__':main_cli()
