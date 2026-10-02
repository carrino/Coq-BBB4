#!/usr/bin/env python3
"""Find nonincreasing weighted pattern potentials with partial decrease.

The linear program allows a zero change on some edges and requires a
strictly negative sum of all edge changes. This can peel a strict subset
of an SCC, using the existing FuelMixTr checker. Every rationalized
coefficient is replayed with exact integer arithmetic before emission.
The usual fueltr_batch CLI is available when executed directly.
"""
import math
from fractions import Fraction

def choose_mix(tbl,n,cs,intra,candidates,delta):
 import numpy as np
 from scipy.optimize import linprog
 from scipy.sparse import csr_matrix,hstack,vstack
 nodes=sorted(cs);index={a:i for i,a in enumerate(nodes)}
 ds=[[delta(p,r,a[0])for a in nodes]for p,r in candidates]
 keep=[i for i,d in enumerate(ds)if min(d)<0]
 if not keep:return None
 edges=list(intra);left=np.array([[ds[i][index[u]]for i in keep]for u,v in edges],dtype=float)
 rows=[];cols=[];vals=[]
 for j,(u,v)in enumerate(edges):rows.extend([j,j]);cols.extend([index[v],index[u]]);vals.extend([1.,-1.])
 pot=csr_matrix((vals,(rows,cols)),shape=(len(edges),len(nodes)));mat=hstack([csr_matrix(left),pot],format='csr')
 aug=vstack([mat,csr_matrix(mat.sum(axis=0))],format='csr');bounds=np.r_[np.zeros(len(edges)),-1]
 result=linprog(np.r_[np.ones(len(keep)),np.zeros(len(nodes))],A_ub=aug,b_ub=bounds,bounds=(0,None),method='highs',options={'time_limit':30.})
 if not result.success:
  return None
 for den in (100,10000):
  fs=[Fraction(float(x)).limit_denominator(den)for x in result.x];scale=math.lcm(*(x.denominator for x in fs))
  ints=[int(x*scale)for x in fs];weights=ints[:len(keep)];phi=dict(zip(nodes,ints[len(keep):]))
  if min(ints)<0 or max(ints)>100000000:continue
  values={a:sum(w*ds[i][j]for i,w in zip(keep,weights))for j,a in enumerate(nodes)}
  changes=[values[u]+phi[v]-phi[u]for u,v in edges]
  if max(changes)<=0 and min(changes)<0:
   return [(w,*candidates[i])for i,w in zip(keep,weights)if w],values,phi
 return None

if __name__ == "__main__":
 from functools import partial
 import fuelmixtr_batch as fm
 fm.ft.instruction_procedure=partial(fm.ft.instruction_procedure.func,mix_finder=choose_mix)
 fm.ft.main()
