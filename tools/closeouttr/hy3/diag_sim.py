"""HY3 tape viewer (untrusted): the last sweep turns at each tape end,
run-length compressed.  python3 tools/closeouttr/hy3/diag_sim.py ROWS.txt [N]"""
import sys; import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from comp import comp
from multiprocessing import Pool
def parse(s):
    T={}
    for i,g in enumerate(s.split('_')):
        for sym in (0,1):
            t=g[3*sym:3*sym+3]
            T[(i,sym)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
def diag(s,N=2000000,K=10):
    T=parse(s); size=2*N+10 if N<100000 else 400000; off=size//2
    tape=bytearray(size); p=off; q=0; lastm=0; lo=hi=off
    L=[];R=[]
    for t in range(N):
        sym=tape[p]; tr=T[(q,sym)]
        if tr is None: return s+' HALT %d'%t
        w,m,nq=tr; tape[p]=w
        if m!=lastm and lastm!=0:
            if p<=lo: L.append((t,p,q,sym))
            elif p>=hi: R.append((t,p,q,sym))
        lastm=m; p+=m; q=nq
        if p<lo: lo=p
        if p>hi: hi=p
        if p<2 or p>size-3: return s+' OOB'
        if (L and L[-1][0]==t) or (R and R[-1][0]==t):
            snap=''.join(str(x) for x in tape[lo:hi+1])
            (L if (L and L[-1][0]==t) else R)[-1]+= (snap,)
            if len(L)>4*K: L=L[-2*K:]
            if len(R)>4*K: R=R[-2*K:]
    out=[s]
    for name,X in (('L',L),('R',R)):
        out.append(' %s-turns: %d kept'%(name,len(X)))
        for x in X[-K:]:
            t,pp,qq,sym,snap=x
            out.append('  %9d %s%d w=%d %s'%(t,'ABCD'[qq],sym,len(snap),comp(snap)))
    return '\n'.join(out)
if __name__=='__main__':
    rows=open(sys.argv[1]).read().split()
    N=int(sys.argv[2]) if len(sys.argv)>2 else 2000000
    with Pool(4) as pool:
        for r in pool.imap(diag, rows): print(r); sys.stdout.flush()
