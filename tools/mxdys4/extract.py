"""Automatic macro-rule extraction: run the raw machine from a symbolic config
in state A and report the transformation to the NEXT state-A configuration."""
import os
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

def run_to_A(tm, cells, pos, cap=100000):
    tape=defaultdict(int)
    for i,c in enumerate(cells): tape[i]=c
    st='A'; t=0
    while True:
        tr=tm[(st,tape[pos])]
        if tr is None: return None
        w,d,n=tr; tape[pos]=w; pos+=1 if d=='R' else -1; st=n; t+=1
        if st=='A': break
        if t>cap: return None
    lo=min(list(tape.keys())+[pos]); hi=max(list(tape.keys())+[pos])
    return (''.join(str(tape[j]) for j in range(lo,hi+1)), pos-lo, lo, t)

CODE=sys.argv[1]; MODE=sys.argv[2]      # 'L1' = left all ones (M4), 'R1' = right all ones (M1)
tm=parse(CODE)
print("### %s  (%s)"%(CODE,MODE))
if MODE=='L1':
    for p in range(0,5):                     # p ones on the left
        for s in (0,1):
            for R in ['','0','1','00','01','10','11','000','001','010','011','100','101','110','111']:
                cells=[1]*p+[s]+[int(c) for c in R]
                r=run_to_A(tm,cells,p)
                if r is None: continue
                W,np_,lo,t=r
                print("  1^%d [A%d] %-4s -> %-14s p=%-2d (shift %d) t=%d"%(p,s,R or '.',W,np_,lo,t))
        print()
else:
    for L in ['','1','0','10','01','11','00','100','101','110','1010']:
        for s in (0,1):
            for R in range(0,5):
                cells=[int(c) for c in L]+[s]+[1]*R
                r=run_to_A(tm,cells,len(L))
                if r is None: continue
                W,np_,lo,t=r
                print("  %-5s [A%d] 1^%d -> %-14s p=%-2d (shift %d) t=%d"%(L or '.',s,R,W,np_,lo,t))
        print()
