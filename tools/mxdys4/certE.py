#!/usr/bin/env python3
"""Measure search with EXTENTS.

  ext l = 0 if l has no S1, else 1 + index of its last S1   (distance head->outermost 1)
  mu = Bo*ones l + Be*ext l + Co*ones r + Ce*ext r + rk(node)
  node = (q, chd l, h, chd r, zl, zr)   with zl = (ext l == 0), zr = (ext r == 0)

Steps (CTape.ctape_move):
  DR  (l,h,r) -> (w::l, chd r, ctl r):
        ones l += w        ones r -= b
        ext l' = (zl ? w : ext l + 1)      ext r' = pred (ext r)
  DL  (l,h,r) -> (ctl l, chd l, w::r):
        ones l -= a        ones r += w
        ext l' = pred (ext l)              ext r' = (zr ? w : ext r + 1)
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
                         else (int(f[0]), 1 if f[1]=='R' else -1, LAB.index(f[2])))
    return tab

def succs(tab,node):
    """(successor node, dOnesL,dExtL,dOnesR,dExtR) list, x/z' over-approximated."""
    q,a,h,b,zl,zr=node
    tr=tab[(q,h)]
    if tr is None: return None
    w,d,q2=tr; out=[]
    if d==1:   # DR
        dOL=w; dOR=-b
        dEL = (w if zl else 1)
        zl2 = (zl and w==0)
        dER = (0 if zr else -1)
        for x in (0,1):
            for zr2 in ([1] if zr else [0,1]):
                if zr and (b or x): continue          # ext r = 0 => whole r blank
                if zr2 and x: continue                # ext(ctl r)=0 => x=0
                out.append(((q2,w,b,x,int(zl2),int(zr2)),dOL,dEL,dOR,dER))
    else:      # DL
        dOL=-a; dOR=w
        dER = (w if zr else 1)
        zr2 = (zr and w==0)
        dEL = (0 if zl else -1)
        for x in (0,1):
            for zl2 in ([1] if zl else [0,1]):
                if zl and (a or x): continue
                if zl2 and x: continue
                out.append(((q2,x,a,w,int(zl2),int(zr2)),dOL,dEL,dOR,dER))
    return out

def orbit_nodes(tab,T=3_000_000):
    tape=defaultdict(int); pos=0; q=0; seen=set()
    lo=hi=0
    for _ in range(T):
        zl = 1 if all(tape[j]==0 for j in range(lo,pos)) else 0
        zr = 1 if all(tape[j]==0 for j in range(pos+1,hi+1)) else 0
        seen.add((q,tape[pos-1],tape[pos],tape[pos+1],zl,zr))
        tr=tab[(q,tape[pos])]
        if tr is None: break
        w,d,q2=tr; tape[pos]=w; pos+=d; q=q2
        lo=min(lo,pos); hi=max(hi,pos)
    return seen

def closure(tab,seed):
    N=set(seed); fr=list(seed)
    while fr:
        n=fr.pop(); s=succs(tab,n)
        if s is None: continue
        for (m,_,_,_,_) in s:
            if m not in N: N.add(m); fr.append(m)
    return N

def search(tab,qgoal,N,MAX=6):
    nodes=sorted(N); idx={n:i for i,n in enumerate(nodes)}
    combos=sorted(product(range(MAX+1),repeat=4),key=sum)
    for (Bo,Be,Co,Ce) in combos:
        edges=[]; ok=True
        for n in nodes:
            if n[0]==qgoal: continue
            s=succs(tab,n)
            if s is None: ok=False; break
            for (m,dOL,dEL,dOR,dER) in s:
                if m not in N: continue
                if m[0]==qgoal: continue
                c = -(Bo*dOL + Be*dEL + Co*dOR + Ce*dER) - 1
                edges.append((idx[n],idx[m],c))
        if not ok: continue
        n_=len(nodes); dist=[0]*n_; neg=False
        for it in range(n_+1):
            ch=False
            for (u,v,c) in edges:
                if dist[u]+c<dist[v]: dist[v]=dist[u]+c; ch=True
            if not ch: break
        else: neg=True
        if neg: continue
        mn=min(dist)
        return (Bo,Be,Co,Ce,{nodes[i]:dist[i]-mn for i in range(n_)})
    return None

if __name__=='__main__':
    for spec in open(sys.argv[1]).read().split():
        tab=parse(spec); N=closure(tab,orbit_nodes(tab))
        res=[]
        for gi,g in enumerate(LAB):
            r=search(tab,gi,N)
            res.append("%s:%s"%(g,("(%d,%d,%d,%d)"%r[:4]) if r else "NONE"))
        print("  %-30s |N|=%-4d %s"%(spec,len(N)," ".join(res)))
