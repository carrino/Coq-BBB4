"""Validate M4's macro rules against the raw simulator."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Sim
CODE='1RB1LD_1LC1RA_0RB0LC_0RA0LD'
# macro state: (p, s, R)  meaning tape = 1^p ++ [s] ++ R   (head on s)
def rules(p,s,R):
    if s==0:
        if R and R[0]==1:                       # (1)
            return ('1', p+2, (R[1] if len(R)>1 else 0), R[2:], 2)
        else:                                   # (2)   R = 0::R'  (or empty)
            R2 = R[1:] if R else []
            if p==0: return ('2e', 1, 1, R2, 7)     # degenerate boot case
            new = [0]*(p-1)+[1]+R2
            return ('2', 1, 0, new, p+7)
    else:                                       # (3)
        if p==0: return ('LOOP',0,1,R,2)
        return ('3', 0, 0, [0]*(p-1)+[1]+R, p+2)

s=Sim(CODE)
for _ in range(7): s.step()          # t=7 : 1[A1] -> use the raw config
def raw(t):
    x=Sim(CODE)
    for _ in range(t): x.step()
    ks=[k for k,v in x.tape.items() if v]
    lo=min(ks+[x.pos]); hi=max(ks+[x.pos])
    return x.st, ''.join(str(x.tape[j]) for j in range(lo,hi+1)), x.pos-lo

# start from t=10: [A0]1  -> p=0,s=0,R=[1]
p,sy,R,t = 0,0,[1],10
ok=bad=0
for i in range(4000):
    r,p,sy,R,c = rules(p,sy,R); t+=c
    st,tape,pos = raw(t)
    exp = ('1'*p + str(sy) + ''.join(map(str,R))).rstrip('0')
    got = tape.rstrip('0')
    # strip leading zeros of expectation frame vs raw frame
    if st=='A' and got.lstrip('0')==exp.lstrip('0') and (len(exp.lstrip('0'))>0 or exp==got): ok+=1
    else:
        bad+=1
        if bad<5: print("MISMATCH t=%d rule=%s macro=1^%d[A%d]%s | raw %s %s"%(t,r,p,sy,''.join(map(str,R)),st,tape))
    R=[x for x in R]
print("M4 macro rules: matched %d / %d (bad %d)"%(ok,ok+bad,bad))
