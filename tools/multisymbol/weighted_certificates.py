#!/usr/bin/env python3
"""Untrusted LP search: graphs.jsonl accepted.jsonl certificates.jsonl. Requires scipy."""
import json,sys,itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
from scipy.sparse.csgraph import connected_components

def scc(n,es):
 a=lil_matrix((n,n))
 for i,j in es:a[i,j]=1
 return connected_components(a.tocsr(),directed=True,connection='strong')[1]
def lp(g,tg,es,kind,k=1):
 ms=g['symbols'];nodes=g['nodes'];tab=g['trans'];nn=len(nodes)
 words=list(itertools.product(range(ms),repeat=k));wi={w:i for i,w in enumerate(words)};m=len(words)
 N=4*m+nn if kind=='w' else 3*ms+nn
 ineq=[];rhs=[];obj=np.zeros(N);crows=[];active={v for e in es for v in e}
 def var(part,w):return part*m+wi[tuple(w[:k])]
 def add(pairs,b=0,edge=False):
  row={}
  for idx,c in pairs:row[idx]=row.get(idx,0)+c
  ineq.append(row);rhs.append(b)
  if edge:
   crows.append(row)
   for j,c in row.items():obj[j]+=c
 if kind=='w':
  for w in itertools.product(range(ms),repeat=k+1):
   add([(var(0,w),-1),(var(2,w[1:]),-1),(var(2,w),2)])
   add([(var(1,w),-1),(var(3,w[1:]),-2),(var(3,w),1)])
  add([(2*m,1)]);add([(3*m,1)])
  for i in active:
   q,l,h,r=nodes[i];add([(var(2,l),-1),(var(3,r),-1),(4*m+i,-1)])
  for i,j in es:
   q,l,h,r=nodes[i];w,d,qn=tab[q*ms+h]
   pass
   if d==-1:add([(var(0,l),-1),(var(1,[w]+r),1),(4*m+j,1),(4*m+i,-2)],edge=True)
   else:add([(var(0,[w]+l),1),(var(1,r),-1),(4*m+j,2),(4*m+i,-1)],edge=True)
  bounds=[(-100,100)]*N;bounds[m]=(0,0)
 else:
  for i,j in es:
   q,l,h,r=nodes[i];w,d,qn=tab[q*ms+h]
   row=[(w,1),(h,-1),(3*ms+j,1),(3*ms+i,-1)]
   row += [(ms+l[0],-1),(2*ms+w,1)] if d==-1 else [(ms+w,1),(2*ms+r[0],-1)]
   add(row,edge=True)
  bounds=[(0,100)]*N
  for i in [0,ms,2*ms]:bounds[i]=(0,0)
 A=lil_matrix((len(ineq),N))
 for i,row in enumerate(ineq):
  for j,c in row.items():A[i,j]=c
 res=linprog(obj,A_ub=A.tocsr(),b_ub=rhs,bounds=bounds,method='highs')
 if not res.success:return None
 ds=[sum(res.x[j]*c for j,c in row.items()) for row in crows]
 if not any(d<-.01 for d in ds):return None
 return [e for e,d in zip(es,ds) if d>=-.01], res.x
from pathlib import Path
from fractions import Fraction
from functools import reduce
from math import lcm,gcd


def integerize(xs):
 fs=[Fraction(float(x)).limit_denominator(100000)for x in xs];den=lcm(*(x.denominator for x in fs));ys=[int(x*den)for x in fs];g=reduce(gcd,ys);return [x//(g or 1)for x in ys]
def solve(g,tg):
 ms=g['symbols'];es=[(i,j)for i,edges in enumerate(g['edges'])for j in edges if g['nodes'][i][0]*ms+g['nodes'][i][2]!=tg and g['nodes'][j][0]*ms+g['nodes'][j][2]!=tg];n=len(g['nodes']);cert=[]
 while es:
  cc=scc(n,es);cross=[(cc[i],cc[j])for i,j in es if cc[i]!=cc[j]];r={c:0 for c in cc}
  for _ in range(len(r)):
   for i,j in cross:r[i]=max(r[i],r[j]+1)
  cert.append(dict(kind='rank',rank=[int(r[c])for c in cc]));es=[e for e in es if cc[e[0]]==cc[e[1]]]
  if not es:return cert
  progress=False;out=[]
  for c in sorted(set(cc)):
   ce=[e for e in es if cc[e[0]]==c]
   if not ce:continue
   for kind in ['linear','w']:
    res=lp(g,tg,ce,kind,1)
    if res is None:continue
    rest,xs=res;cert.append(dict(kind=kind,values=integerize(xs),active=sorted({v for e in ce for v in e})))
    progress=True;ce=rest;break
   out+=ce
  if not progress:return None
  es=out
 return cert

def wallcert(g,tg,k):
 ms=g['symbols'];tab=g['trans'];entry={tr[2]for i,tr in enumerate(tab)if i!=tg and tr and tr[1]==-1};todo=[];seen=set();guards=set()
 def addword(w):
  if w in guards:return
  guards.add(w)
  for q in entry:todo.append((q,w[1:],w[0],()))
 addword((0,)*k)
 while todo:
  q,l,h,r=c=todo.pop()
  if c in seen:continue
  seen.add(c)
  if q*ms+h==tg:continue
  w,d,qn=tab[q*ms+h]
  if d==-1:todo.append((qn,l[1:],l[0],(w,)+r))
  elif not r:addword((w,)+l)
  else:todo.append((qn,(w,)+l,r[0],r[1:]))
 return dict(k=k,guards=sorted(guards),inside=sorted(seen))

def wall(g,tg,k):
 ms=g['symbols'];tab=g['trans'];entry={tr[2] for i,tr in enumerate(tab) if i!=tg and tr and tr[1]==-1}
 todo=[];seen=set();guards=set()
 def addword(w):
  if w in guards:return
  guards.add(w)
  for q in entry:todo.append((q,w[1:],w[0],()))
 addword((0,)*k)
 while todo:
  c=todo.pop()
  if c in seen:continue
  if len(seen)>5000:return False
  seen.add(c);q,l,h,r=c
  if q*ms+h==tg:continue
  tr=tab[q*ms+h]
  if tr is None:return False
  w,d,qn=tr
  if d==-1:
   if not l:return False
   todo.append((qn,l[1:],l[0],(w,)+r))
  else:
   if not r:addword((w,)+l)
   else:todo.append((qn,(w,)+l,r[0],r[1:]))
 return True
if __name__=='__main__':
 good={(x['machine'],x['mirror'])for x in map(json.loads,open(sys.argv[2]))if x['ok']};done=set();out=open(sys.argv[3],'w')
 for g in map(json.loads,open(sys.argv[1])):
  if(g['machine'],g['mirror'])not in good or g['machine']in done:continue
  tgcert={}
  for tg in range(g['states']*g['symbols']):
   if tg in g['ranked']:continue
   cs=solve(g,tg);assert cs is not None
   k=next(k for k in range(1,9)if wall(g,tg,k));tgcert[tg]=dict(**wallcert(g,tg,k),components=cs)
  out.write(json.dumps(dict(graph=g,certs=tgcert))+'\n');out.flush();done.add(g['machine'])
  if len(done)%20==0:print(len(done),flush=True)
