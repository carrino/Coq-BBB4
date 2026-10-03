# LE11 (untrusted): see SCOPING_INSTR 7.4.LE11.  Run from this directory.
from sim import *
from two_level import step
import sys
spec=sys.argv[1]; anchor=sys.argv[2]; Rpre=sys.argv[3]; Z=sys.argv[4]; O=sys.argv[5]; mark=sys.argv[6]; tstart=int(sys.argv[7]); tend=int(sys.argv[8])
def cells(u,v,y):
    L=''.join('10' if b else '00' for b in u)+'1'+''.join('10' if b else '00' for b in v)
    R=Rpre+''.join(O if b else Z for b in y)+mark
    return L.rstrip('0'),R.rstrip('0')
def allt(l): return all(l)
def good(u,v,y):
    if allt(y): return False
    if u and u[0]==1 and not allt(u): return True
    if allt(u) and (not v or v[0]==0): return True
    return False
m=M(spec); s=None; nxt=None; n=0; fired=set(); bad=0; goodn=0
def tapeLR():
    ks=[k for k,v in m.tape.items() if v]; lo=min(ks+[m.pos]); hi=max(ks+[m.pos])
    L=''.join(str(m.tape.get(i,0)) for i in range(m.pos-1,lo-1,-1)).rstrip('0')
    R=''.join(str(m.tape.get(i,0)) for i in range(m.pos+1,hi+1)).rstrip('0')
    return L,R
lastt=0
while m.t<tend:
    cur=m.q+str(m.tape.get(m.pos,0))
    if cur==anchor and m.t>=tstart:
        L,R=tapeLR()
        if s is None:
            if L=='1':
                body=R[len(Rpre):]
                body=body[:len(body)-len(mark)] if mark else body
                y=[]; ok=True
                for i in range(0,len(body),len(O)):
                    w=body[i:i+len(O)]
                    if w==O: y.append(1)
                    elif w==Z: y.append(0)
                    else: ok=False
                if ok and cells([],[],y)==(L,R):
                    s=([],[],y); print('start',m.t,s); nxt=step(*s)[:3]; fired=set(); lastt=m.t
        elif (L,R)==cells(*nxt):
            g=good(*s)
            if g:
                goodn+=1
                if len(fired)<8: print('GOOD BUT MISSING',s,sorted(fired)); bad+=1
            s=nxt; nxt=step(*s)[:3]; fired=set(); n+=1; lastt=m.t
    if s is not None: fired.add(cur)
    m.step()
print('macros',n,'good',goodn,'bad',bad,'last match',lastt)
