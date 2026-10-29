"""S064 bounded direct controls and binary phase trajectory; native provenance only."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2LB3RA2LA_2RB1RA1RB3LB'
TABLE=codes(MACHINE)
BOUND=2**54

def run(config,n):
    q,l,h,r=config;l,r=list(l),list(r)
    for _ in range(n):
        v=TABLE[4*q+h];q=v&1;x=v//4
        if v&2:l=[x]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[x]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def front(q,l,r):return q,list(l),(r[0]if r else 0),list(r[1:])
def back(q,l,r):return q,list(l[1:]),(l[0]if l else 0),list(r)
def tail(e):return [2]if e else[]
def main(a,b,e):return 0,[3]*a+[1]*b+tail(e),0,[]
def P(b,c,d,e,t):return back(1,[1]*b+tail(e),[2]*c+[3]*d+[t])
def drift(n,e):return 1,[1]*n+tail(e),0,[]

def phase(b,c,d,e):
    elapsed=edges=0
    while d:
        if b:
            z=min(b,d);elapsed+=2*z*z+(2*c+1)*z;b-=z;c+=2*z;d-=z
        elif c:
            elapsed+=c+5;b,c,d,e=c-1+e,2,d-1,1-e
        else:return None
        edges+=1
        assert edges<=64
    return b,c,e,elapsed,edges

def nxt(a,b,e):
    bb,c,ee,t,edges=phase(b,0,a,e);base=1+a+t
    if not bb:return ('M',0,c+1+ee,1-ee,base+c+2,edges)
    if not c:return ('M',1,bb,ee,base+4,edges)
    bbb,cc,eee,u,edge2=phase(bb-1,2,c-1,ee);elapsed=base+2*c+5+u+cc+2
    if not bbb:return ('D',cc+1+eee,0,1-eee,elapsed,edges+edge2)
    return ('M',cc+1,bbb,eee,elapsed,edges+edge2)

def raw_return(a,b,e):
    q,l,h,r=main(a,b,e)
    for t in range(1,1000001):
        q,l,h,r=run((q,l,h,r),1)
        if h==0 and r==[]:
            if q:return 'D',None,None,None,t
            aa=0
            while aa<len(l)and l[aa]==3:aa+=1
            bb=aa
            while bb<len(l)and l[bb]==1:bb+=1
            ee=len(l)-bb
            assert ee in(0,1)and l[bb:]==tail(ee)
            return 'M',aa,bb-aa,ee,t
    raise AssertionError('direct return budget')

def direct_blank(budget=5000000):
    tape={};q=p=0;lo=0;hi=-1;events=[]
    for t in range(budget+1):
        if q==0 and p>hi:
            w=[tape.get(x,0)for x in range(p-1,lo-1,-1)]
            a=b=0
            while a<len(w)and w[a]==3:a+=1
            while a+b<len(w)and w[a+b]==1:b+=1
            e=len(w)-a-b
            assert e in(0,1)and w[a+b:]==tail(e)
            events.append(dict(time=t,a=a,b=b,e=e))
        if t==budget:break
        v=TABLE[4*q+tape.get(p,0)];tape[p]=v//4;lo=min(lo,p);hi=max(hi,p)
        p+=1 if v&2 else-1;q=v&1
    for x,y in zip(events,events[1:]):
        kind,a,b,e,elapsed,_=nxt(x['a'],x['b'],x['e'])
        assert kind=='M'and(a,b,e)==(y['a'],y['b'],y['e'])and elapsed==y['time']-x['time']
    return events

def check():
    assert TABLE==[5,9,14,8,11,6,7,13]
    ctx=[[]]+[[x]for x in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    sweeps=pairs=batches=resets=terminals=0
    for n,l,r in itertools.product(range(7),ctx,ctx):
        assert run(back(0,[3]*n+l,r),n)==back(0,l,[2]*n+r)
        assert run(front(0,l,[2]*n+r),n)==front(0,[3]*n+l,r)
        assert run(back(1,[3]*n+l,r),n)==back(1,l,[3]*n+r)
        assert run(front(1,l,[2]*n+r),n)==front(1,[1]*n+l,r);sweeps+=4
        assert run(back(1,[1]+l,[2]*n+[3]+r),2*n+3)==back(1,l,[2]*(n+2)+r);pairs+=1
    for z,b,c,d,e,t in itertools.product(range(6),range(4),range(4),range(4),range(2),range(4)):
        assert run(P(b+z,c,d+z,e,t),2*z*z+(2*c+1)*z)==P(b,c+2*z,d,e,t);batches+=1
    for c,d,e,t in itertools.product(range(1,10),range(1,10),range(2),range(4)):
        assert run(P(0,c,d,e,t),c+5)==P(c-1+e,2,d-1,1-e,t);resets+=1
    for c,e in itertools.product(range(10),range(2)):
        assert run(P(0,c,0,e,1),c+2)==main(0,c+1+e,1-e)
        assert run(P(0,c,0,e,2),c+2)==drift(c+1+e,1-e);terminals+=2
    for b,c,e in itertools.product(range(1,10),range(10),range(2)):
        assert run(P(b,c,0,e,2),c+2)==main(c+1,b,e);terminals+=1
        if c:
            assert run(P(b,c,0,e,1),2*c+5)==P(b-1,2,c-1,e,2);terminals+=1
        else:
            assert run(P(b,0,0,e,1),4)==main(1,b,e);terminals+=1
    grid=drift_controls=0
    for a,b,e in itertools.product(range(18),range(1,13),range(2)):
        z=nxt(a,b,e);r=raw_return(a,b,e)
        assert z[0]==r[0]and z[4]==r[4]
        if z[0]=='M':assert z[1:4]==r[1:4]
        else:
            assert run(main(a,b,e),z[4])==drift(z[1],z[3]);drift_controls+=1
        grid+=1
    assert phase(0,0,1,0)is None and phase(0,0,1,1)is None
    assert run((0,[],0,[]),3)==main(0,1,1)
    direct=direct_blank()
    a,b,e,elapsed,index=0,1,1,3,1;resets_seen=[dict(index=1,time=3,b=1,e=1)]
    digest=hashlib.sha256();maxedges=0
    while index<262144:
        before=(a,b,e);z=nxt(a,b,e);kind,A,B,E,t,edges=z
        elapsed+=t;index+=1;maxedges=max(maxedges,edges)
        digest.update((str((index,elapsed,z))+'\n').encode())
        if kind=='D':
            final=dict(cut_index=index,time=elapsed,previous_main=list(before),left_ones=A,left_tail2=E)
            break
        a,b,e=A,B,E
        if not a:resets_seen.append(dict(index=index,time=elapsed,b=b,e=e))
    else:raise AssertionError('main budget')
    assert final==dict(cut_index=242779,time=12762141566885339,previous_main=[212693,273462,1],left_ones=486158,left_tail2=0)
    assert elapsed<BOUND<205770076433044242247860 and maxedges==42
    return dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(TABLE)),state_bound=BOUND,
                arbitrary_context_sweeps=sweeps,arbitrary_context_pairs=pairs,batch_controls=batches,
                reset_controls=resets,terminal_controls=terminals,main_grid_controls=grid,synthetic_drift_controls=drift_controls,
                direct_blank_steps=5000000,direct_main_cuts=direct,all_ones_resets=resets_seen,
                accelerated_main_edges=index-1,maximum_phase_edges_per_main=maxedges,
                accelerated_sequence_sha256=digest.hexdigest(),drift_entry=final,
                negative_controls=['b=c=0,d>0 phase is rejected rather than claimed safe',
                                   'synthetic main seeds can drift; actual blank drift is separately computed',
                                   '242779-cut actual blank run eventually drifts, so a universal state-zero recurrence claim is false'])

def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py']
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths})
    path=ROOT/'research/burn33-s064-native.json';s=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==s
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(s)
    print(json.dumps({k:v for k,v in row.items()if k not in('direct_main_cuts','all_ones_resets')}),flush=True)
if __name__=='__main__':main_cli()
