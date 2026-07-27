from snfit import *
from sim import Sim, LAB
TR=[(q,y) for q in range(4) for y in range(2)]
def allrecords(spec, steps):
    s=Sim(spec); cum={k:0 for k in TR}; loB=hiB=0; out=[(0,s.q,'L',0,s.tape_str(),dict(cum))]
    for _ in range(steps):
        k=s.step()
        if k is None: return out,True
        cum[k]+=1
        if s.pos<loB: loB=s.pos; out.append((s.t,s.q,'L',s.pos-s.lo,s.tape_str(),dict(cum)))
        elif s.pos>hiB: hiB=s.pos; out.append((s.t,s.q,'R',s.hi-s.pos,s.tape_str(),dict(cum)))
    return out,False
