#!/usr/bin/env python3
"""Untrusted correlated-block finder for transition closeout AST_52.

Run from any directory (the finder needs SciPy for affine rankings)::

    python3 tools/closeouttr/ast_cone.py find certificates.jsonl
    python3 tools/closeouttr/ast_cone.py batch certificates.jsonl --number 52

The source row reaches C0 at step 446 with the nearest-first left word
1^4 (011)^3 (11011)^3 0 1^2. Successive large sweeps add one 011 block
and two 11011 blocks. Families retain that relation as a nonnegative
integer cone b + A*z, rather than giving each block an independent length.
Small primitive rays can widen a family; every resulting leaf and every
ranking are subsequently checked by the existing TriGlueTr checker.
No new trusted checker is introduced. The second row is a state renaming
of the same family system, reached one step earlier from its blank tape.
"""
import argparse
import copy
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hy3_ti as H
from cbt import write_batch

T, B, C, LC = H.T, H.B, H.C, H.T.LC
T.GEN_UNITS = H.UNIT_SETS[1][1]
T.MAXFAM = 500
T.MAXLEAF = 6000

def solve(A,b):
 n=len(A)
 if n==0:return [] if not any(b) else None
 m=[list(map(Fraction,[a[i] for a in A]+[b[i]])) for i in range(len(b))];r=0;rs=[]
 for j in range(n):
  piv=next((k for k in range(r,len(m)) if m[k][j]),None)
  if piv is None:return None
  m[r],m[piv]=m[piv],m[r];v=m[r][j];m[r]=[x/v for x in m[r]]
  for k in range(len(m)):
   if k!=r and m[k][j]:
    v=m[k][j];m[k]=[x-v*y for x,y in zip(m[k],m[r])]
  rs.append(r);r+=1
 if any(not any(row[:-1]) and row[-1] for row in m):return None
 return [m[r][-1] for r in rs]
def cols(ex):
 ks=sorted({k for b,lin in ex for k,m in lin})
 return [(k,[sum(m for j,m in e[1] if j==k) for e in ex]) for k in ks]
def prim(v):
 d=math.gcd(*v)
 return [x//d for x in v] if d else v
class Fam:
 def __init__(self,key,b,A):
  self.key=key;self.q,self.h,self.sL,self.sR=key;self.b=b;self.A=A;self.n=max(1,len(A));self.version=0;self.lb=[0]*self.n
 def pattern(self):
  out=[];i=0
  for sh in (self.sL,self.sR):
   side=[]
   for s in sh:
    if s[0]=='L':side.append(s);continue
    terms=[(k,a[i]) for k,a in enumerate(self.A) if a[i]]
    if not terms:side.append(('B',s[1],(self.b[i],())))
    else:
     for j,(k,a) in enumerate(terms):side.append(('B',s[1],(self.b[i] if j==0 else 0,((k,a),))))
    i+=1
   out.append(side)
  return out
 def value(self,ex):
  src=[([x[0]-b for x,b in zip(ex,self.b)],None)]+[(v,k) for k,v in cols(ex)]
  dst=[[0,[]] for _ in range(self.n)]
  for v,k in src:
   z=solve(self.A,v)
   if z is None or any(x<0 or x.denominator!=1 for x in z):return None
   for j,x in enumerate(z):
    if k is None:dst[j][0]=int(x)
    elif x:dst[j][1].append((k,int(x)))
  return [(b,tuple(lin)) for b,lin in dst]
 def widen(self,ex):
  b=list(self.b);A=copy.deepcopy(self.A)
  eb=[e[0] for e in ex];diff=[x-y for x,y in zip(eb,b)]
  z=solve(A,diff)
  if z is None:
   if all(x>=0 for x in diff) and max(prim(diff))<=2:A.append(prim(diff))
   elif all(x<=0 for x in diff) and max(prim([-x for x in diff]))<=2:A.append(prim([-x for x in diff]));b=eb
   else:return False
  elif any(x.denominator!=1 for x in z):return False
  else:
   nb=[v+sum(min(0,int(x))*a[i] for a,x in zip(A,z)) for i,v in enumerate(b)]
   if any(x<0 for x in nb):return False
   b=nb
  for k,v in cols(ex):
   z=solve(A,v)
   if z is None:
    if max(prim(v))>2:return False
    A.append(prim(v))
   elif any(x<0 or x.denominator!=1 for x in z):return False
  trial=Fam(self.key,b,A)
  if trial.value(ex) is None:return False
  if b==self.b and A==self.A:return False
  self.b,self.A=b,A;self.n=max(1,len(A));self.version+=1;self.lb=[self.version]*self.n
  return True
class Explorer(T.Explorer):
 def __init__(self,tab):super().__init__(tab,set())
 def fam_of(self,q,h,L,R):
  L=T.generalize(L);R=T.generalize(R);key=(q,h,T.shape(L),T.shape(R));ex=T.exps(L)+T.exps(R)
  for i,F in enumerate(self.fams):
   if F.key==key and F.value(ex) is not None:return i,ex,False
  for i,F in enumerate(self.fams):
   if F.key==key and F.widen(ex):return i,ex,True
  if len(self.fams)>=T.MAXFAM:raise T.Fail('family cap')
  b=[e[0] for e in ex];A=[]
  for k,v in cols(ex):
   if solve(A,v) is None:A.append(prim(v))
  F=Fam(key,b,A)
  if F.value(ex) is None:raise T.Fail('noncone family')
  i=len(self.fams);self.fams.append(F);return i,ex,True
 def constant_match(self,q,h,L,R):
  L=T.generalize(C.nstrip(C.norm(L)));R=T.generalize(C.nstrip(C.norm(R)));key=(q,h,T.shape(L),T.shape(R));ex=T.exps(L)+T.exps(R)
  return any(F.key==key and F.A and F.value(ex)is not None for F in self.fams)
oldleaf=T.leaf_run;X=None
# Fully fixed leaves can run through the whole finite boundary transient.
def leaf(tabw,fam,R,na,p):
 if not all(m==0 for m,c in R):return oldleaf(tabw,fam,R,na,p)
 sub=C.rsub(R);pat=fam.pattern();Lz=[C.seg_subst(sub,x) for x in pat[0]];Rz=[C.seg_subst(sub,x) for x in pat[1]]
 lp,_=T.cprefix(Lz,0);rp,_=T.cprefix(Rz,0);c0=(fam.q,(lp,(),0,0,()),fam.h,(rp,(),0,0,()));c=c0;chain=[]
 for j in range(10000):
  tr=tabw[(c[0],c[2])]
  if tr is None:raise T.Fail('halt fixed branch')
  d=tr[1];side=c[3] if d>0 else c[1];st=('SWin',1) if side[0] else ('SWinR' if d>0 else 'SWinL',1)
  r=LC.sstep(tabw,True,True,st,c)
  if r is None:raise T.Fail('fixed branch refused')
  c=r[0];chain.append(st);L=C.ss_segs(c[1],0);Ri=C.ss_segs(c[3],0)
  if X.constant_match(c[0],c[2],L,Ri):return dict(c0=c0,el=True,er=True,chain=T.merge_chain(chain),j=0,nL=len(Lz),nR=len(Rz),c1=c,q1=c[0],h1=c[2],endL=L,endR=Ri,Lz=Lz,Rz=Rz)
 raise T.Fail('fixed branch too long')

SOURCE = "0RB1LD_1RC1RB_1LA1RA_1LC0LA"
SIBLING = "1RB1RA_1LC1RC_0RA1LD_1LB0LC"


def fired_in(cert, tab):
    return [set(C.leaf_fired(tab, dict(chain=lf["chain"], el=lf["el"],
                                     er=lf["er"], c0=lf["c0"])))
            for lf in cert["leaves"]]


def validate(cert):
    tab = T.parse(cert["spec"])
    err = T.fams_ok(tab, cert)
    if err is not None:
        raise T.Fail("family replay: %s" % err)
    if not T.boot_ok(cert, tab):
        raise T.Fail("boot replay")
    err = T.live_ok(cert, tab, fired_in(cert, tab))
    if err is not None:
        raise T.Fail("liveness replay: %s" % err)


def find(periods):
    global X
    tab = T.parse(SOURCE)
    q, L, h, R, _ = T.run_conc(tab, 446)
    L = T.generalize(C.nstrip(C.norm([("L", L)])))
    R = T.generalize(C.nstrip(C.norm([("L", R)])))
    key = (q, h, T.shape(L), T.shape(R))
    X = Explorer(tab)
    F = Fam(key, [4, 3, 3, 2], [[0, 1, 2, 0]])
    X.fams = [F]
    X.boot = (0, [(v, ()) for v in F.b])
    todo, iterations = [0], 0
    start = time.monotonic()
    try:
        T.leaf_run = leaf
        while todo:
            i = todo.pop(0)
            if i in todo:
                continue
            X.explore_fam(i, todo)
            iterations += 1
            if iterations > 10000:
                raise T.Fail("iteration cap")
        cert = B.assemble(X, 446, False, set())
    finally:
        T.leaf_run = oldleaf
    cert.update(spec=SOURCE, qh=False)
    print("closed", len(cert["fams"]), "families,", len(cert["leaves"]),
          "leaves in", round(time.monotonic() - start, 3), "s", flush=True)
    fired = fired_in(cert, tab)
    for period in periods:
        ranks = T.live_search(cert, tab, fired, period)
        if isinstance(ranks, dict):
            cert.update(ranks)
            break
    else:
        raise T.Fail("no affine instruction rankings")
    validate(cert)
    sibling = T.jsonable(cert)
    perm = [2, 0, 1, 3]
    for fam in sibling["fams"]:
        fam["q"] = perm[fam["q"]]
    for lf in sibling["leaves"]:
        lf["c0"][0] = perm[lf["c0"][0]]
    for instruction in sibling["pins"]:
        instruction[0] = perm[instruction[0]]
    for instruction, _ in sibling["ranks"]:
        instruction[0] = perm[instruction[0]]
    sibling.update(spec=SIBLING, t0=445)
    sibling = T.detuple(sibling)
    validate(sibling)
    return [cert, sibling]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    finder = sub.add_parser("find")
    finder.add_argument("output", type=Path)
    finder.add_argument("--periods", type=int, nargs="+", default=[1, 2, 3, 4, 6])
    batcher = sub.add_parser("batch")
    batcher.add_argument("certificates", type=Path)
    batcher.add_argument("--number", type=int, default=52)
    batcher.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        certs = find(args.periods)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text("".join(json.dumps(T.jsonable(c)) + "\n" for c in certs))
    else:
        certs = [T.detuple(json.loads(line)) for line in args.certificates.read_text().splitlines()
                 if line.strip()]
        for cert in certs:
            validate(cert)
        write_batch("AST", args.number,
                    ["From BBB4.Checkers Require Import LapDecider.",
                     "From BBB4.Counters Require Import TriGlueTr."],
                    [(c["spec"], T.render(c)) for c in certs],
                    "correlated block cones and affine instruction rankings",
                    overwrite=args.overwrite)


if __name__ == "__main__":
    main()
