# LE11 (untrusted): see SCOPING_INSTR 7.4.LE11.  Run from this directory.
from two_level3 import *
def val(l): return sum(b<<i for i,b in enumerate(l))
def bits(x,n): return [(x>>i)&1 for i in range(n)]
def run_pass(s, limit=10**8):
    n=0
    while n<limit:
        p,u,v,y=s
        nxt,k=step(s)
        n+=1
        s=nxt
        if s[0]=='P1' and not s[2] and k!='n' and k not in('top1',): return s,n,k
    return None
# era start 3
s=('P1',[0],[],[1,1,0,1,1,1,0,0,0,1,0,1,1,0,1,1,1,0,0,0,0,0,0,0])
for era in range(3,8):
    p,u,v,y=s
    W=len(y); X0=val(u+[1]); D0=(1<<W)-1-val(y)
    Xo=X0+D0
    lu=Xo.bit_length()-1
    print('era',era,'W',W,'X0',X0,'valy0',val(y),'X_ovf',Xo,'|u_ovf|',lu,'W-|u|',W-lu)
    uo=bits(Xo,lu)
    s=('P1',uo,[],[1]*W)
    r=run_pass(s, limit=5*10**7)
    if r is None: print('pass too long / failed'); break
    s,n,k=r
    print('  pass macros',n,'end kind',k,'new state u',s[1][:8],'|y|',len(s[3]))
