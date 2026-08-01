"""Macro system for M1 = 1RB1LC_0LC0RB_1LA1RD_0LA0RD, validated against raw sim."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Sim
CODE='1RB1LC_0LC0RB_1LA1RD_0LA0RD'

# config: (W list of cells 0..w-1, p head).  Invariant: W[p+1..w-1] all 1.
def rules(W,p):
    w=len(W); R=w-1-p
    if W[p]==0:
        if R>=2:
            W2=W[:]; W2[p]=1
            for i in range(p+1,w-1): W2[i]=0
            return ('1',W2,w-2,R+3)
        else:
            W2=W[:]; W2[p]=1
            return ('2',W2,p,4)
    else:
        left = W[p-1] if p>=1 else 0
        if left==0:
            if p>=2:
                W2=W[:]; W2[p-1]=1
                return ('4',W2,p-2,2)
            else:
                # head runs off the left edge: widen
                W2=[0]+[1]*w if p==1 else [0,0]+[1]*w
                # p==1: cells0,1 ->1, rest already 1 => tape 1^w, new blank at left
                if p==1: return ('4e',[0]+[1]*w,0,2)
                else:    return ('6',[0]+[1]*(w+1),0,2)
        else:
            W2=W[:]
            for i in range(p,w): W2[i]=0
            return ('5',W2,w-1,R+4)

def macro_run(nsteps):
    # start: t=4 config [A1] tape "1": W=[1], p=0
    W=[1]; p=0; t=4; out=[]
    for _ in range(nsteps):
        r,W,p,c = rules(W,p); t+=c
        out.append((t,r,''.join(map(str,W)),p))
    return out

def raw_config(t):
    s=Sim(CODE)
    for _ in range(t): s.step()
    ks=[k for k,v in s.tape.items() if v]
    lo=min(ks+[s.pos]); hi=max(ks+[s.pos])
    return s.st, lo, ''.join(str(s.tape[j]) for j in range(lo,hi+1)), s.pos-lo

ok=0; bad=0
for (t,r,Wstr,p) in macro_run(400):
    st,lo,tape,pos = raw_config(t)
    # macro W is cells 0..w-1 of the epoch frame; compare state A and local word
    exp = Wstr + '1'*0
    # build expected raw tape: W then 1^R
    w=len(Wstr); R=w-1-p
    full = Wstr[:p+1] + '1'*R
    full = full.rstrip('0')
    got  = tape.rstrip('0')
    # align: macro frame's cell0 may be left of lo
    if st!='A' or got!=full or (pos != p - (0 if lo>=0 else 0)):
        pass
    if st=='A' and got==full: ok+=1
    else:
        bad+=1
        if bad<6: print("MISMATCH t=%d rule=%s macro=%s p=%d | raw st=%s tape=%s pos=%d lo=%d"%(t,r,Wstr,p,st,tape,pos,lo))
print("matched %d / %d  (bad %d)"%(ok,ok+bad,bad))

print("\n=== macro trace ===")
W=[1]; p=0; t=4
for i in range(70):
    r,W,p,c = rules(W,p); t+=c
    print("%-4s w=%-3d p=%-3d t=%-7d %s" % (r,len(W),p,t,''.join(map(str,W))))
