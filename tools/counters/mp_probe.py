#!/usr/bin/env python3
"""Scan for the MARKER-AFTER encoding (John's reading of
0RB---_0RC0LD_1LD1RC_0LA1LB): nearest-first word [b0,1,b1,1,...,b_{n-1},1],
MSB outermost, marker cell AFTER each bit.  Ip/Jp put the marker BEFORE,
Kp has none -- so this is a fourth encoding with no Coq definition yet."""
import json, sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0,'/home/user/Coq-BBB4/tools/counters')
from emit_interleave import LAB, Raw, strip0
from mirror_common import mirror_spec

def Mp(v):
    """value -> nearest-first marker-after word"""
    w=[]
    while v:
        w += [v & 1, 1]; v >>= 1
    return w

def dec(w):
    if len(w)%2 or not w: return None
    bits=[]
    for i in range(0,len(w),2):
        if w[i+1]!=1: return None
        bits.append(w[i])
    if bits[-1]!=1: return None
    return sum(b<<i for i,b in enumerate(bits))

def nrm(c):
    q,l,h,r=c; return (q,tuple(strip0(l)),h,tuple(strip0(r)))

def probe(rspec):
    for mirror in (False,True):
        spec = mirror_spec(rspec) if mirror else rspec
        raw=Raw(spec); cfg=(0,[],0,[]); fam=defaultdict(list)
        for t in range(1,30000):
            cfg=raw.step(cfg)
            if cfg is None: break
            q,l,h,r=cfg
            if h==0 and not strip0(r) and l:
                base=tuple(strip0(l))
                for tl in range(0,3):
                    w=base[:len(base)-tl] if tl else base
                    v=dec(list(w))
                    if v is not None:
                        fam[(q,tl,base[len(base)-tl:] if tl else ())].append(v); break
        if not fam: continue
        (q,tl,T0),vals = max(fam.items(), key=lambda kv: len(kv[1]))
        # longest consecutive run
        run=brun=1; 
        for k in range(1,len(vals)):
            run = run+1 if vals[k]==vals[k-1]+1 else 1
            brun=max(brun,run)
        if brun < 20: continue
        # lap costs from this anchor
        def lap(mv,maxs=120000):
            c=(q,Mp(mv)+list(T0),0,[]); tg=nrm((q,Mp(mv+1)+list(T0),0,[]))
            for t in range(1,maxs):
                c=raw.step(c)
                if c is None: return None
                if nrm(c)==tg: return t
            return None
        ints={}
        for j in range(0,4):
            mv=(1<<(j+1))+(1<<j)-1 if j else 2
            n=lap(mv)
            if n is None: ints=None; break
            ints[j]=n
        aff=None
        if ints:
            ds=[ints[j+1]-ints[j] for j in range(3)]
            aff = ds[0] if len(set(ds))==1 else None
        return {'spec':rspec,'mirror':mirror,'edge':LAB[q],'tail':list(T0),
                'run':brun,'ints':ints,'slope':aff}
    return {'spec':rspec,'mp':False}

if __name__=='__main__':
    specs=[x.strip() for x in open(sys.argv[1]) if x.strip()]
    with ProcessPoolExecutor(max_workers=6) as p, open(sys.argv[2],'w') as o:
        for r in p.map(probe, specs, chunksize=4):
            o.write(json.dumps(r)+'\n'); o.flush()
