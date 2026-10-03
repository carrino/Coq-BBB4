# LE11 (untrusted): see SCOPING_INSTR 7.4.LE11.  Run from this directory.
from two_level3 import *
import sys
def val(l): return sum(b<<i for i,b in enumerate(l))
def bits(x,n): return [(x>>i)&1 for i in range(n)]
for W in range(2,int(sys.argv[1])+1):
    res={}
    for lu in range(0,W+2):
        bad=0; tot=0; maxlen=0
        for x in range(1<<lu):
            u=bits(x,lu); s=('P1',u,[],[1]*W); n=0; tot+=1
            try:
                while True:
                    nxt,k=step(s); n+=1; s=nxt
                    if s[0]=='P1' and not s[2] and k not in ('n','top1'): break
                    if n>10**6: break
            except AssertionError: bad+=1
            maxlen=max(maxlen,n)
        res[lu]=(bad,tot)
    print(W, {k:v[0] for k,v in res.items()})
