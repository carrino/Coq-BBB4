"""S070 exact scanner controls and finite DFA provenance, without proof credit."""
import argparse,hashlib,itertools,json
from pathlib import Path
from generate_pipeline_examples import codes
ROOT=Path(__file__).resolve().parents[1]
MACHINE='1LB2RA1RA0RA_2RB1LA3LB2LB'
TABLE=codes(MACHINE)
ODD=[2,1,0,0,0,2,2]
EVEN=[2,0,2,2,1,0,2,2]
MODEL=ROOT/'research/burn35-s070-grammar-model.json'
INDEPENDENT=ROOT/'research/burn35-s070-model-independent-check.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(config,n):
    q,l,h,r=config;l,r=list(l),list(r)
    for _ in range(n):
        v=TABLE[4*q+h];q=v&1;x=v//4
        if v&2:l=[x]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[x]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def front(q,l,r):return q,list(l),(r[0]if r else 0),list(r[1:])
def back(q,l,r):return q,list(l[1:]),(l[0]if l else 0),list(r)
def main(w,r=()):return 0,list(w),0,list(r)
def write(h):return {1:2,2:1,3:0}[h]
def revword(R):return [write(x)for x in R[::-1]]
def scan(mode,w,Rlen=0):
    # Modes0=B3 pending0,1=A,2=B1,3=copy. Returns relative output and exact native cost.
    w=list(w);out=[];elapsed=0;j=0
    while True:
        if mode==3:return out+w[j:],elapsed
        if j==len(w):
            if mode==0:return None
            p,cost=([2,1],6+Rlen)if mode==1 else([1],4+Rlen)
            return out+p,elapsed+cost
        h=w[j];j+=1
        if h==3:return None
        if mode==0:
            if h==0:mode,p,dt=0,[1],3
            elif h==1:mode,p,dt=1,[0,2],1
            else:mode,p,dt=0,[0],1
        elif mode==1:
            if h:return out+[2 if h==1 else 1]+w[j:],elapsed+2+Rlen
            mode,p,dt=2,[2],1
        else:
            if h==0:return out+[1]+w[j:],elapsed+4+Rlen
            if h==1:mode,p,dt=1,[2],1
            else:mode,p,dt=0,[],1
        out+=p;elapsed+=dt;Rlen+=1

def T(w):
    z=scan(2,w)
    return None if z is None else([2]+z[0],1+z[1])
def G(w):
    z=scan(0,w)
    return None if z is None else[0]+z[0]

def check():
    assert TABLE==[5,10,6,2,11,4,13,9]
    assert sha(MODEL)=='5799ccc7ce51cf7c5b3fca568ed2d5a1876565576f2e3659d515da23caf7f73a'
    model=json.loads(MODEL.read_text())[-1];D=model['transitions'];A=model['accepting'];H=set(map(tuple,model['prefix_relation']))
    def feed(q,w):
        for h in w:q=D[h][q]
        return q
    assert A[feed(0,[1])]and(0,0,D[0][0])in H
    for i,m,o in H:
        for h in range(3):
            mm,p=model['transducer'][m][h];assert(D[h][i],mm,feed(o,p))in H
        if A[i]:
            p=model['end_outputs'][m];assert p is not None and A[feed(o,p)]
    assert json.loads(INDEPENDENT.read_text())['source_sha256']==sha(MODEL)
    ctx=[[]]+[[h]for h in range(4)]+[list(w)for w in itertools.product(range(4),repeat=2)]
    positive=[[]]+[[h]for h in(1,2,3)]+[list(w)for w in itertools.product((1,2,3),repeat=2)]
    left=[list(w)for n in range(4)for w in itertools.product(range(3),repeat=n)]
    scanner=0
    for mode,w,R,r in itertools.product(range(3),left,positive,ctx):
        z=scan(mode,w,len(R))
        if z is None:continue
        if mode==0:initial=back(1,w,[3]+R+r);acc=revword(R)
        elif mode==1:initial=back(0,w,[1]+R+r);acc=revword(R)+[2]
        else:initial=back(1,w,[1]+R+r);acc=revword(R)+[2]
        assert run(initial,z[1])==front(0,acc+z[0],r),(mode,w,R,r,z)
        scanner+=1
    main_controls=rejected=0
    for n in range(8):
        for w in itertools.product(range(3),repeat=n):
            z=T(w)
            if z is None:rejected+=1;continue
            assert run(main(w),z[1])==main(z[0]),(w,z)
            main_controls+=1
    outer=0
    for n in range(5):
        for w in itertools.product(range(3),repeat=n):
            a=T(ODD+list(w));assert a[0]==EVEN+list(w)
            assert run(main(ODD+list(w)),a[1])==main(EVEN+list(w));outer+=1
            image=G(w)
            if image is not None:
                b=T(EVEN+list(w));assert b[0]==ODD+image
                assert run(main(EVEN+list(w)),b[1])==main(ODD+image);outer+=1
    assert run(main([]),35)==main(ODD+[1])
    # A weak paired-marker grammar can lose its marker; this is excluded by the DFA.
    bad=[2,1,0,0,1];bad_sequence=[bad]
    for _ in range(3):bad=T(bad)[0];bad_sequence.append(bad)
    assert T(bad)is None
    # Direct actual blank cuts are checked against the exact two-outer-phase map.
    tape={};q=p=0;lo=hi=0;cuts=[]
    for t in range(1000001):
        if q==0 and tape.get(p,0)==0 and p>=hi:
            w=[tape.get(x,0)for x in range(p-1,lo-1,-1)];cuts.append(dict(time=t,left=w))
        if t==1000000:break
        v=TABLE[4*q+tape.get(p,0)];tape[p]=v//4;lo=min(lo,p);hi=max(hi,p)
        p+=1 if v&2 else-1;q=v&1
        while hi>lo and tape.get(hi,0)==0:hi-=1
    for x,y in zip(cuts,cuts[1:]):
        z=T(x['left']);assert z is not None and z[0]==y['left']and z[1]==y['time']-x['time']
    normalized=[]
    for x,y in zip(cuts[3::2],cuts[5::2]):
        assert x['left'][:7]==ODD and y['left'][:7]==ODD
        w=x['left'][7:];assert A[feed(0,w)]and G(w)==y['left'][7:]
        normalized.append(dict(time=x['time'],length=len(w)))
    return dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(TABLE)),state_bound=0,
                model_sha256=sha(MODEL),independent_model_check_sha256=sha(INDEPENDENT),
                DFA_states=8,prefix_relation_entries=len(H),finite_transition_controls=3*len(H),
                arbitrary_context_scanner_controls=scanner,main_word_controls=main_controls,rejected_main_words=rejected,
                outer_phase_controls=outer,actual_entry_steps=35,direct_blank_steps=1000000,
                direct_main_cuts=len(cuts)-1,direct_normalized_cycles=len(normalized),
                last_direct_normalized_cut=normalized[-1],
                negative_controls=dict(weak_marker_sequence=bad_sequence,final_scanner_rejected=True,
                  empty_G_rejected=G([])is None,twos_G_rejected=G([2,2])is None),
                contribution='Root synthesized and independently validated the frozen8-state DFA; remaining_state_solver proved its finite laws, universal scanner translation and full state recurrence in Coq.')

def main_cli():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    row=check();paths=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py',MODEL,INDEPENDENT]
    data=dict(scope=__doc__,checked_state_families=0,rows=[row],source_sha256={str(p.relative_to(ROOT)):sha(p)for p in paths})
    path=ROOT/'research/burn35-s070-native.json';s=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.check:assert path.read_text()==s
    elif path.exists():raise ValueError('Frozen native report exists; use --check')
    else:path.write_text(s)
    print(json.dumps(row),flush=True)
if __name__=='__main__':main_cli()
