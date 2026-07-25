#!/usr/bin/env python3
"""The hammer probe (TERMINOLOGY.md #hammer): out-degree vs history.

Two measurements per (machine, k, n, t):
 1. FULL-CLOSURE out-degree: grow() the branching closure; report the
    fraction of nodes with out-degree 1 and the max out-degree.
 2. RHO TRAJECTORY (the actually load-bearing condition): grow the gram
    sets LEAN -- seed windows + donations from trajectory nodes only --
    and follow the unique-successor path from a0.  Report RHO(tau,lam)
    if the path closes into a cycle with singleton succs throughout,
    else BRANCH@i / STUCK / CAP.

If a bounded k drives ~every unboarded machine to RHO, the determinism
soundness lemma boards the bulk uniformly (never-QH iff every obliged
state is on the cycle; tail-only states are quiet => R_QH) and the
measure search evaporates.  UNTRUSTED - a targeting experiment only.
"""
import sys, os, json
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nghist_prove as P

TRAJ_CAP = 6000      # max trajectory steps per walk
ROUNDS = 80          # max donation-fixpoint rounds

def donate(tm, a):
    """Mirror grow()'s donation for a single node."""
    q,(lw,s,rw)=a
    tr=tm[q][P.bit(s)]
    if tr is None: return None
    return ('L',lw) if tr[1]=='R' else ('R',rw)

def traj_walk(tm,k,n,lset,rset,a0):
    """Follow unique successors from a0 with FIXED sets, accumulating the
    donations of every visited node.  Returns (verdict, dl, dr) where
    verdict is ('RHO',tau,lam,traj) | ('BRANCH',i,deg) | ('HALT',i) |
    ('NOWIN',i) | ('CAP',)."""
    pos={a0:0}; traj=[a0]; dl=set(); dr=set()
    a=a0
    for i in range(TRAJ_CAP):
        d=donate(tm,a)
        if d is None: return (('HALT',i),dl,dr)
        if d[0]=='L': dl.add(d[1])
        else: dr.add(d[1])
        sc=P.hng_succs(tm,k,n,lset,rset,a)
        if sc is None: return (('NOWIN',i),dl,dr)   # near window not in set yet
        if len(sc)!=1: return (('BRANCH',i,len(sc)),dl,dr)
        b=sc[0]
        if b in pos:
            tau=pos[b]; lam=len(traj)-tau
            return (('RHO',tau,lam,traj),dl,dr)
        pos[b]=len(traj); traj.append(b); a=b
    return (('CAP',),dl,dr)

def rho_probe(tm,k,n,t):
    """Lean-set fixpoint: seed windows + trajectory donations only.  A verdict
    is final only when a round added no new donations (sets stable)."""
    sd=P.seed(tm,k,n,t)
    if sd is None: return ('HALT',-1)
    a0,lset,rset=sd
    lset=set(lset); rset=set(rset)
    for r in range(ROUNDS):
        res,dl,dr=traj_walk(tm,k,n,lset,rset,a0)
        nl=lset|dl; nr=rset|dr
        stable = (nl==lset and nr==rset)
        if res[0]=='RHO' and stable:
            _,tau,lam,traj=res
            cyc=set(a[0] for a in traj[tau:])
            tail=set(a[0] for a in traj[:tau])
            obliged=P.visited_states_prefix(tm,k,t)|cyc|tail
            quiet=sorted(obliged-cyc)
            return ('RHO',tau,lam,''.join(sorted(cyc)),''.join(quiet))
        if res[0] in ('BRANCH','HALT','CAP') and stable:
            return res
        if res[0]=='NOWIN' and stable:
            return res           # stuck with nothing left to donate
        lset,rset=nl,nr
    return ('NOFIX',)

def closure_probe(tm,k,n,t,fuel=20000):
    g=P.grow(tm,k,n,t,fuel)
    if g is None: return None
    a0,lset,rset,seen,edges=g
    degs=[len(edges[a]) for a in seen]
    d1=sum(1 for d in degs if d==1)
    return dict(nctx=len(seen), d1=d1, frac1=round(d1/len(seen),3), maxdeg=max(degs))

GRID=[(2,2),(4,2),(6,2),(8,2),(2,3),(4,3),(6,3),(2,4),(4,4),(12,2),(12,3)]
TS=[150,600]

def probe_machine(m):
    tm=P.decode(m)
    out={'m':m}
    best=None
    for (k,n) in GRID:
        for t in TS:
            r=rho_probe(tm,k,n,t)
            out['rho_k%d_n%d_t%d'%(k,n,t)]=list(r[:3])
            if r[0]=='RHO' and best is None:
                best=(k,n,t)+tuple(r[1:])
        if best: break               # smallest determinizing (k,n) found
    out['best']=best
    # full-closure out-degree at k=2 and k=4 (cheap reference)
    for k in (2,4):
        c=closure_probe(tm,k,2,40)
        out['cls_k%d'%k]=c
    return out

def main():
    sample_file=sys.argv[1]
    outf=sys.argv[2]
    ms=[l.strip() for l in open(sample_file) if l.strip()]
    n=int(os.environ.get('PROBE_LIMIT', len(ms)))
    ms=ms[:n]
    with open(outf,'w') as f, ProcessPoolExecutor(max_workers=2) as ex:
        for i,r in enumerate(ex.map(probe_machine, ms, chunksize=4)):
            f.write(json.dumps(r)+'\n')
            if (i+1)%50==0:
                f.flush(); sys.stderr.write('%d/%d\n'%(i+1,len(ms)))
    sys.stderr.write('DONE %d\n'%len(ms))

if __name__=='__main__':
    main()
