"""plain simulator for the BLC2 measurements (UNTRUSTED)."""
import sys
def parse(s):
    tab={}
    for q,part in enumerate(s.split('_')):
        for h in range(2):
            t=part[3*h:3*h+3]
            tab[(q,h)] = None if t[2] in 'Z-' else (int(t[0]), 1 if t[1]=='R' else -1, ord(t[2])-65)
    return tab
def rle(cells):
    out=[];i=0
    s=''.join(map(str,cells))
    return s
def run(spec, n, every=None, show=None):
    tab=parse(spec); tape={}; pos=0; q=0
    lo=hi=0
    for t in range(n):
        h=tape.get(pos,0)
        if show and show(t,q,h,pos,tape):
            cells=[tape.get(i,0) for i in range(lo,hi+1)]
            s=''.join(map(str,cells)); p=pos-lo
            yield t,q,h,s[:p]+'['+'ABCD'[q]+']'+s[p:]
        w,d,nq=tab[(q,h)]; tape[pos]=w; pos+=d; q=nq; lo=min(lo,pos); hi=max(hi,pos)
import re
def compress(s):
    # runs of 1s as (1)^n
    return re.sub(r'1{4,}', lambda m:'(1)^%d'%len(m.group()), s)
if __name__=='__main__':
    spec=sys.argv[1]; n=int(sys.argv[2]); tgt=sys.argv[3]  # e.g. C0
    q0='ABCD'.index(tgt[0]); h0=int(tgt[1])
    for t,q,h,s in run(spec,n,show=lambda t,q,h,pos,tape:(q,h)==(q0,h0)):
        print(t, compress(s.strip('0') if False else s))
