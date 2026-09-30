"""HY3 residue probe (untrusted, SCOPING_INSTR.md 7.4.HY3): the tape at the
last sweep turns (most frequent state, 3M steps) split into long periodic
blocks (>= 16 cells, unit <= 6).  Prints, per side, the block counts seen
and how many block shapes there are.

    python3 tools/closeouttr/hy3/shape.py ROWS.txt > shape.tsv
"""
import sys, collections
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from diag_sim import parse
from multiprocessing import Pool
def prim(u):
    n=len(u)
    for d in range(1,n+1):
        if n%d==0 and u[:d]*(n//d)==u: return u[:d]
    return u
def blocks(s, mincells=16):
    # greedy: find long periodic runs with unit<=6
    i=0; out=[]; lit=''
    n=len(s)
    while i<n:
        best=None
        for k in range(1,7):
            u=s[i:i+k]
            if len(u)<k: break
            if prim(u)!=u: continue
            j=i
            while s[j:j+k]==u: j+=k
            if j-i>=mincells and (best is None or j-i>best[1]): best=(u,j-i)
        if best:
            if lit: out.append(('L',lit)); lit=''
            u,L=best; out.append(('B',u,L//len(u))); i+=(L//len(u))*len(u)
        else: lit+=s[i]; i+=1
    if lit: out.append(('L',lit))
    return out
def run(s,N=3000000):
    T=parse(s); size=400000; off=size//2
    tape=bytearray(size); p=off; q=0; lastm=0; lo=hi=off
    snaps={'L':[], 'R':[]}
    for t in range(N):
        sym=tape[p]; tr=T[(q,sym)]
        if tr is None: return None
        w,m,nq=tr; tape[p]=w
        if m!=lastm and lastm!=0 and (p<=lo or p>=hi) and t>N//3:
            sd='L' if p<=lo else 'R'
            snaps[sd].append((t,q,sym,bytes(tape[lo:hi+1])))
            if len(snaps[sd])>400: snaps[sd]=snaps[sd][-200:]
        lastm=m; p+=m; q=nq
        if p<lo: lo=p
        if p>hi: hi=p
        if p<2 or p>size-3: return None
    return snaps
def analyze(s):
    sn=run(s)
    if sn is None: return s+'\tERR'
    res=[]
    for sd in 'LR':
        X=sn[sd]
        if len(X)<6: res.append(sd+':few%d'%len(X)); continue
        # pick most frequent (q,sym)
        c=collections.Counter((x[1],x[2]) for x in X)
        key=c.most_common(1)[0][0]
        Y=[x for x in X if (x[1],x[2])==key][-30:]
        B=[blocks(''.join(map(str,y[3]))) for y in Y]
        nb=[sum(1 for b in bb if b[0]=='B') for bb in B]
        shapes=collections.Counter(tuple((b[0],b[1]) if b[0]=='B' else ('L',) for b in bb) for bb in B)
        res.append('%s:n=%d nb=%s shapes=%d last=%s'%(sd,len(Y),sorted(set(nb)),len(shapes), ' '.join((b[1] if b[0]=='L' else '(%s)^%d'%(b[1],b[2])) for b in B[-1])[:150]))
    return s+'\t'+'\t'.join(res)
if __name__=='__main__':
    rows=open(sys.argv[1]).read().split()
    with Pool(4) as pool:
        for r in pool.imap(analyze, rows): print(r); sys.stdout.flush()
