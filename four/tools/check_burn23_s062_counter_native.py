"""Bounded S062 protected-word and dead-boundary controls; no kernel credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB3RA1RA_3RB3LA0RB2LB'
TABLE=codes(MACHINE)
def run(conf,count):
    q,l,h,r=conf;l,r=list(l),list(r)
    for _ in range(count):
        c=TABLE[4*q+h];q=c&1;v=c//4
        if c&2:l=[v]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[v]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def front(q,l,r):return q,list(l),(r[0]if r else 0),list(r[1:])
def back(q,l,r):return q,list(l[1:]),(l[0]if l else 0),list(r)
def decode(w):return [3 if x==2 else 1 for x in w[::-1]]
def guard(w,a):return list(w)+[2,3]+[2]*a+[1]
def main(a,u,v):return 0,[3]*a+[1,1]+list(u)+list(v),0,[]
def dead(l,r):return 0,list(l),0,list(r)
def guarded(r):
    if all(x==3 for x in r):return True
    if not r or r[-1]!=1:return False
    w=r[:-1]
    while w and w[-1]==2:w=w[:-1]
    return len(w)>=2 and w[-2:]==[2,3] and all(x in[2,3]for x in w)
def safe(c):
    q,l,h,r=c
    if q or h:return False
    if all(x in[0,3]for x in l)and guarded(r):return True
    if r:return False
    k=0
    while k<len(l)and l[k]==3:k+=1
    if l[k:k+2]!=[1,1]:return False
    seen=False
    for x in l:
        if x not in[0,1,3]or(x==1 and seen):return False
        if x==0:seen=True
    return True

def words(alphabet,n):return [list(w)for k in range(n+1)for w in itertools.product(alphabet,repeat=k)]
def next_cut(c,budget=3000):
    for n in range(1,budget+1):
        c=run(c,1)
        if safe(c):return n,c
    raise AssertionError(('cut budget',c))
def check():
    assert TABLE==[5,9,14,6,15,12,3,9]
    ctx=words(range(4),2);ws=words([2,3],4);uv=words([1,3],2);vv=words([0,3],2)
    sweeps=pairs=launches=protected=maincuts=deadcuts=0
    for n in range(7):
        for l,r in itertools.product(ctx,repeat=2):
            assert run(back(1,[3]*n+l,r),n)==back(1,l,[2]*n+r)
            assert run(front(1,l,[2]*n+r),n)==front(1,[0]*n+l,r)
            sweeps+=2
    for w,l,r in itertools.product(ws,ctx,ctx):
        assert run(front(0,l,w+r),len(w))==front(0,decode(w)+l,r);sweeps+=1
    for l,r in itertools.product(ctx,repeat=2):
        assert run(back(1,[1,1]+l,r),2)==back(1,l,[2,3]+r);pairs+=1
        assert run(back(1,[1,3]+l,r),3)==front(0,[1,1]+l,r);launches+=1
        assert run(back(0,[3]+l,[3]+r),2)==front(0,[1,1]+l,r);launches+=1
    for a,w,u,v in itertools.product(range(7),ws,uv,vv):
        assert run(back(1,[1,3]+u+v,guard(w,a)),len(w)+3*a+10)==main(a+1,decode(w)+[1,1]+u,v)
        protected+=1
    for a,u,v in itertools.product(range(3),words([1,3],5),words([0,3],5)):
        if v and v[-1]!=3:continue
        c=main(a,u,v);assert safe(c);n,c1=next_cut(c);assert n>0 and safe(c1);maincuts+=1
    rights=[[3]*n for n in range(7)]+[guard(w,a)for w,a in itertools.product(ws,range(6))]
    for l,r in itertools.product(words([0,3],5),rights):
        n,c1=next_cut(dead(l,r));assert n>0 and safe(c1);deadcuts+=1
    assert run((0,[],0,[]),5)==main(0,[],[])
    for r in ctx:assert run(dead([3],r),5)==dead([3],[3]+r)
    assert run(dead([],[1]),17)==(1,[3,3,3,0,0,3,3],0,[])
    assert run((0,[1,3],0,[]),13)==(1,[0,0,3,3],0,[])
    assert run((0,[1,1,0,1,3],0,[]),33)==(1,[0,3,0,0,0,3,3],0,[])
    # One direct, unaccelerated blank run validates the physical cut grammar.
    d={};q=p=0;lo=hi=0;cuts=[];last=[0,0];maxgap=[0,0]
    for t in range(400001):
        maxgap[q]=max(maxgap[q],t-last[q]);last[q]=t
        if q==0 and d.get(p,0)==0 and (not d or p>hi):
            l=[d.get(x,0)for x in range(p-1,lo-1,-1)]
            assert safe((q,l,0,[]))if t else l==[]
            cuts.append(dict(time=t,head=p,length=len(l)))
        c=TABLE[4*q+d.get(p,0)];v=c//4
        if v:d[p]=v;lo=min(lo,p);hi=max(hi,p)
        elif p in d:
            del d[p]
            if p==lo:lo=min(d,default=p)
            if p==hi:hi=max(d,default=p)
        p+=1 if c&2 else-1;q=c&1
    return dict(machine=MACHINE,code=sum(c*17**i for i,c in enumerate(TABLE)),state_bound=0,
                arbitrary_context_sweeps=sweeps,pair_controls=pairs,launch_controls=launches,
                protected_double_launch_controls=protected,main_cut_controls=maincuts,dead_cut_controls=deadcuts,
                actual_entry_steps=5,direct_blank_steps=400000,direct_right_cuts=len(cuts),
                first_direct_right_cuts=cuts[:12],last_direct_right_cuts=cuts[-8:],direct_maximum_state_gaps=maxgap,
                negative_controls=['unguarded dead right1','single leading1 with left3','a1 left of0 in the tail'])
def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn23-s062-counter-native.json';text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==text
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(text)
    print(json.dumps({k:v for k,v in row.items()if'cuts'not in k}),flush=True)
if __name__=='__main__':main_cli()
