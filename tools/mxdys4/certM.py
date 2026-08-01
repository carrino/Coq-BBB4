#!/usr/bin/env python3
"""Measure search: k-cell window + CAPPED extents ml = min(ext l, 2).

node = (q, a_{k-1}..a_0, h, b_0..b_{k-1}, ml, mr)
mu   = Bo*ones l + Be*ext l + Co*ones r + Ce*ext r + rk(node)

ext(ctl u) = pred (ext u);  ext(w::u) = if ext u =? 0 then w else S (ext u)
so   DR: ml' = (ml=0 ? w : 2)          [exact]
         mr' in {0}      if mr<=1,  in {1,2} if mr=2
     DL: mirror.
Consistency: ml=0 -> every window cell of l is 0; ml=1 -> a0=1 and the rest 0.
"""
import sys
from itertools import product
from collections import defaultdict
LAB='ABCD'

def parse(spec):
    tab={}
    for qi,part in enumerate(spec.split('_')):
        for s in (0,1):
            f=part[3*s:3*s+3]
            tab[(qi,s)]=(None if f in ('---','1RZ')
                         else (int(f[0]),1 if f[1]=='R' else -1,LAB.index(f[2])))
    return tab

def cons(A,m):
    """A = [a_{k-1},...,a_0] (a_0 = chd, last element)."""
    if m==0: return not any(A)
    if m==1: return A[-1]==1 and not any(A[:-1])
    return True

def mk(q,A,h,B_,ml,mr): return (q,)+tuple(A)+(h,)+tuple(B_)+(ml,mr)

def succs(tab,node,k):
    q=node[0]; A=list(node[1:1+k]); h=node[1+k]; B_=list(node[2+k:2+2*k]); ml=node[-2]; mr=node[-1]
    if not cons(A,ml) or not cons(list(reversed(B_)),mr): return []
    tr=tab[(q,h)]
    if tr is None: return None
    w,d,q2=tr; out=[]
    if d==1:   # DR: l'=w::l, h'=b_0, r'=ctl r
        dOL=w; dOR=-B_[0]
        dEL=(w if ml==0 else 1); ml2=(w if ml==0 else 2)
        dER=(0 if mr==0 else -1)
        mr2s=[0] if mr<=1 else [1,2]
        A2=A[1:]+[w]
        for mr2 in mr2s:
            for x in (0,1):
                B2=B_[1:]+[x]
                if not cons(list(reversed(B2)),mr2): continue
                out.append((mk(q2,A2,B_[0],B2,ml2,mr2),dOL,dEL,dOR,dER))
    else:      # DL: l'=ctl l, h'=a_0, r'=w::r
        dOL=-A[-1]; dOR=w
        dER=(w if mr==0 else 1); mr2=(w if mr==0 else 2)
        dEL=(0 if ml==0 else -1)
        ml2s=[0] if ml<=1 else [1,2]
        B2=[w]+B_[:-1]
        for ml2 in ml2s:
            for x in (0,1):
                A2=[x]+A[:-1]
                if not cons(A2,ml2): continue
                out.append((mk(q2,A2,A[-1],B2,ml2,mr2),dOL,dEL,dOR,dER))
    return out

def ext(cells):
    e=0
    for i,c in enumerate(cells):
        if c: e=i+1
    return e

def orbit_nodes(tab,k,T=3_000_000):
    tape=defaultdict(int); pos=0; q=0; seen=set(); lo=hi=0
    for _ in range(T):
        L=[tape[pos-1-i] for i in range(0,max(1,pos-lo)+2)]
        R=[tape[pos+1+i] for i in range(0,max(1,hi-pos)+2)]
        ml=min(ext(L),2); mr=min(ext(R),2)
        A=[tape[pos-i] for i in range(k,0,-1)]; B_=[tape[pos+i] for i in range(1,k+1)]
        seen.add(mk(q,A,tape[pos],B_,ml,mr))
        tr=tab[(q,tape[pos])]
        if tr is None: break
        w,d,q2=tr; tape[pos]=w; pos+=d; q=q2; lo=min(lo,pos); hi=max(hi,pos)
    return seen

def closure(tab,seed,k):
    N=set(seed); fr=list(seed)
    while fr:
        n=fr.pop(); s=succs(tab,n,k)
        if s is None: continue
        for t in s:
            if t[0] not in N: N.add(t[0]); fr.append(t[0])
    return N

def try_coef(tab,qgoal,N,k,coef):
    Bo,Be,Co,Ce=coef
    nodes=sorted(N); idx={n:i for i,n in enumerate(nodes)}; edges=[]
    for n in nodes:
        if n[0]==qgoal: continue
        s=succs(tab,n,k)
        if s is None: return ('HALT',n)
        for (m,dOL,dEL,dOR,dER) in s:
            if m not in N or m[0]==qgoal: continue
            edges.append((idx[n],idx[m],-(Bo*dOL+Be*dEL+Co*dOR+Ce*dER)-1))
    n_=len(nodes); dist=[0]*n_; pre=[-1]*n_
    for it in range(n_+1):
        last=-1
        for (u,v,c) in edges:
            if dist[u]+c<dist[v]: dist[v]=dist[u]+c; pre[v]=u; last=v
        if last==-1:
            mn=min(dist); return ('OK',(coef,{nodes[i]:dist[i]-mn for i in range(n_)}))
    v=last
    for _ in range(n_): v=pre[v]
    cyc=[v]; u=pre[v]
    while u!=v: cyc.append(u); u=pre[u]
    cyc.append(v)
    return ('NEG',[nodes[i] for i in reversed(cyc)])

def search(tab,qgoal,N,k,MAX):
    lastcyc=None
    for coef in sorted(product(range(MAX+1),repeat=4),key=lambda c:(sum(c),c)):
        r=try_coef(tab,qgoal,N,k,coef)
        if r[0]=='OK': return r[1],None
        if r[0]=='HALT': return None,r[1]
        lastcyc=r[1]
    return None,lastcyc

if __name__=='__main__':
    k=int(sys.argv[2]); MAX=int(sys.argv[3])
    for spec in open(sys.argv[1]).read().split():
        tab=parse(spec); orb=orbit_nodes(tab,k); N=closure(tab,orb,k)
        res=[]
        for gi,g in enumerate(LAB):
            r,cyc=search(tab,gi,N,k,MAX)
            res.append("%s:%s"%(g,str(r[0]) if r else "NONE"))
        print("  k=%d %-30s |N|=%-5d %s"%(k,spec,len(N)," ".join(res)))
