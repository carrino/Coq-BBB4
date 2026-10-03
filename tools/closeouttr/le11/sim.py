# LE11 (untrusted): a plain TM simulator, M(spec).step() / .show().
import sys
def parse(spec):
    T={}
    for i,blk in enumerate(spec.split('_')):
        q='ABCD'[i]
        for s in (0,1):
            t=blk[3*s:3*s+3]
            if t[2] in 'Z-H' : T[(q,s)]=None; continue
            T[(q,s)]=(int(t[0]),1 if t[1]=='R' else -1,t[2])
    return T
class M:
    def __init__(s,spec):
        s.T=parse(spec); s.tape={}; s.pos=0; s.q='A'; s.t=0
    def step(s):
        r=s.tape.get(s.pos,0); w,d,q=s.T[(s.q,r)]
        s.last=(s.q,r)
        s.tape[s.pos]=w; s.pos+=d; s.q=q; s.t+=1
    def show(s,lo=None,hi=None):
        ks=[k for k,v in s.tape.items() if v] + [s.pos]
        lo=min(ks) if lo is None else lo; hi=max(ks) if hi is None else hi
        out=''
        for i in range(lo,hi+1):
            c=str(s.tape.get(i,0))
            out+= ('['+s.q+c+']') if i==s.pos else c
        return out
