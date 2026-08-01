import sys
from collections import defaultdict
def parse(code):
    tm={}
    for si,part in enumerate(code.split('_')):
        st="ABCD"[si]
        for sym in (0,1):
            f=part[3*sym:3*sym+3]
            tm[(st,sym)]=None if f=='---' else (int(f[0]),f[1],f[2])
    return tm
N=3_000_000
for code in sys.argv[1:]:
    tm=parse(code); tape=defaultdict(int); pos=0; st='A'
    last=defaultdict(lambda:0); maxgap=defaultdict(int); gapat=defaultdict(int)
    lo=hi=0
    for t in range(N):
        g=t-last[st]
        if g>maxgap[st]: maxgap[st]=g; gapat[st]=(t, hi-lo+1)
        last[st]=t
        tr=tm[(st,tape[pos])]
        if tr is None: break
        w,d,n=tr; tape[pos]=w; pos+=1 if d=='R' else -1; st=n
        lo=min(lo,pos); hi=max(hi,pos)
    print(code)
    for q in "ABCD":
        print("   %s  maxgap=%-8d at t=%-9s width=%-5s   (final width %d)" %
              (q,maxgap[q],gapat[q][0] if gapat[q] else '-',gapat[q][1] if gapat[q] else '-',hi-lo+1))
