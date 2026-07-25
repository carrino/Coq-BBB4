#!/usr/bin/env python3
"""Cluster machines by LAP PHASE SIGNATURE: trace one interior lap from the
derived anchor, segment it into monotone head-direction phases, and emit a
signature (dir, state_in->state_out) per phase.  One signature = one lap shape
= one template."""
import sys, json
sys.path.insert(0,'/home/user/Coq-BBB4/tools/counters')
import emit_interleave as E
from concurrent.futures import ProcessPoolExecutor
from collections import Counter

def sig(spec, fp):
    r=fp.get(spec)
    if r is None or r.get('cls')!='COUNTER': return None
    try:
        for enc in ('Jp','Ip'):
            try:
                edge,tail,p0=E.derive_tail(spec,r['edge'],encname=enc); break
            except E.DeriveError: continue
        else: return None
        Ei=E.LAB.index(edge); raw=E.Raw(spec); encf=E.ENC[enc]
        JI=3; m=(1<<(JI+1))+(1<<JI)-1
        n,_=E.raw_lap(raw,Ei,encf,m,tail)
        cfg=(Ei,encf(m)+tail,0,[]); pos=0; tr=[]
        for t in range(n):
            q,l,h,rr=cfg
            tr.append((E.LAB[q],pos))
            nx=raw.step(cfg)
            if nx is None: break
            pos+=(len(nx[1])-len(l)); cfg=nx
        ph=[]; i=0
        while i<len(tr)-1:
            d=(tr[i+1][1]>tr[i][1])-(tr[i+1][1]<tr[i][1])
            j=i
            while j<len(tr)-1 and ((tr[j+1][1]>tr[j][1])-(tr[j+1][1]<tr[j][1]))==d: j+=1
            ph.append(f"{'+' if d>0 else '-' if d<0 else '0'}{tr[i][0]}{tr[j][0]}")
            i=j
        return {'m':spec,'enc':enc,'nphase':len(ph),'nsteps':n,'sig':'|'.join(ph)}
    except Exception:
        return None

FP=None

def _init():
    global FP
    if FP is None:
        FP=E.load_fp('/home/user/Coq-BBB4/tools/counters/wave8_fingerprints_v2.jsonl')

def work(m):
    _init()
    return sig(m, FP)

if __name__=='__main__':
    ms=[l.strip() for l in open(sys.argv[1]) if l.strip()]
    out=[]
    with ProcessPoolExecutor(max_workers=4) as ex:
        for r in ex.map(work, ms, chunksize=4):
            if r: out.append(r)
    json.dump(out, open(sys.argv[2],'w'))
    c=Counter(r['sig'] for r in out)
    print(f"machines with a derivable anchor + traceable lap: {len(out)}/{len(ms)}")
    print(f"distinct lap shapes: {len(c)}")
    print(f"\nphase-count distribution: {dict(Counter(r['nphase'] for r in out))}")
    print("\ntop lap shapes (count, nphase, signature):")
    for s,n in c.most_common(12):
        ex1=next(r for r in out if r['sig']==s)
        print(f"  {n:>4}  nphase={ex1['nphase']}  {s[:70]}")
