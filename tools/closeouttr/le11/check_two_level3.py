# LE11 (untrusted): see SCOPING_INSTR 7.4.LE11.  Run from this directory.
from sim import *
from two_level3 import *
import sys
spec=sys.argv[1]; t0=int(sys.argv[2]); t1=int(sys.argv[3])
m=M(spec); s=None; n=0; kinds={}
while m.t<t1:
    if m.q=='B' and m.tape.get(m.pos,0)==0 and m.t>=t0:
        ks=[k for k,v in m.tape.items() if v]; lo=min(ks); hi=max(ks)
        L=''.join(str(m.tape.get(i,0)) for i in range(m.pos-1,lo-1,-1)).rstrip('0')
        R=''.join(str(m.tape.get(i,0)) for i in range(m.pos+1,hi+1))
        if s is None:
            if L=='1':
                y=[1 if R[2*i:2*i+2]=='11' else 0 for i in range(len(R)//2-1)]
                if cells(('P1',[],[],y))==(L,R): s=('P1',[],[],y); nxt,k=step(s); print('start',m.t,s); lastt=m.t
        elif (L,R)==cells(nxt):
            kinds[k]=kinds.get(k,0)+1; s=nxt; nxt,k=step(s); n+=1; lastt=m.t
            if k not in ('n',): pass
    m.step()
print('macros',n,'last',lastt,kinds)
