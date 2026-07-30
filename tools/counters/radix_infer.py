#!/usr/bin/env python3
"""UNTRUSTED: infer the counter's RADIX, not just its alphabet.

tools/counters/alphabet_infer.py reads the digit words off the tape, but its
shape is a positive-recursion --

    E xH = C     E (xO q) = A ++ E q     E (xI q) = B ++ E q

-- so it can only ever return a BASE-2 counter, and so can
tools/kcopy_classify.py, whose whole vocabulary (KCOPY<k>, SEP<k>) is
"one BIT per k cells".  Every counter alphabet in theories/Counters (Ip, Jp,
Kp, Dp, Bp, Mp) is base 2 as well.

Some of the residue is not base 2.  1RB---_0LB1RC_0RD0RC_1LB1LD is a base-3
counter: after the wall the tape is 2-cell digits over {00,01,11}, the anchor
snapshots decode to 1,2,3,... consecutively over 10^4 visits, and the lap is
4 + 4j in the carry length.  counter_encodings.tsv calls it KCOPY1, which is
why emit_kp.py derives 0 of 17 on these rows: it is fitting the wrong radix.

This tool searches (anchor side, anchor state, digit width, leading trim,
digit order) for ANY radix 2..4 making the snapshots consecutive, and reports
the lap law per carry length so the affine/non-affine split is visible.

  python3 tools/counters/radix_infer.py [rowfile]

Nothing here carries proof weight.
"""
import sys, itertools
sys.path.insert(0,'tools/reachsti')
from cert_search import parse, LAB
W=800; OFF=400

def anchors(spec,T=60000,side='L'):
    tab=parse(spec); tape=bytearray(W); p=OFF; q=0; lo=hi=OFF; out=[]
    for i in range(T):
        edge = (p==lo) if side=='L' else (p==hi)
        if edge: out.append((i,q,''.join(str(c) for c in tape[lo:hi+1])))
        tr=tab[(q,tape[p])]
        if tr is None: break
        tape[p]=tr[0]; p+=tr[1]; q=tr[2]; lo=min(lo,p); hi=max(hi,p)
    return out

def try_fit(words, k, pre, side):
    bodies=[]
    for w in words:
        b = w[pre:] if side=='L' else w[::-1][pre:]
        if len(b)%k: b = b + '0'*(k-len(b)%k)
        bodies.append([b[t:t+k] for t in range(0,len(b),k)])
    alpha=sorted({d for b in bodies for d in b})
    r=len(alpha)
    if r<2 or r>4: return None
    for perm in itertools.permutations(alpha):
        val={d:i for i,d in enumerate(perm)}
        if val[perm[0]]!=0: pass
        seq=[]
        for b in bodies:
            v=0
            for d in reversed(b): v=v*r+val[d]
            seq.append(v)
        if all(seq[t+1]==seq[t]+1 for t in range(len(seq)-1)) and len(set(seq))==len(seq):
            return r,k,pre,perm,seq[0],len(seq)
    return None

def carry(v,r):
    j=0
    while v%r==r-1: j+=1; v//=r
    return j

rowfile = sys.argv[1] if len(sys.argv)>1 else 'tools/reachsti/drozd26.txt'
for m in open(rowfile).read().split():
    found=None
    for side in ('L','R'):
        A=anchors(m,side=side)
        for want in range(4):
            S=[(i,w) for (i,q,w) in A if q==want]
            if len(S)<30: continue
            words=[w for _,w in S]; idx=[i for i,_ in S]
            for k in (1,2,3):
                for pre in (0,1,2):
                    f=try_fit(words,k,pre,side)
                    if f:
                        r,k2,pre2,perm,v0,n=f
                        gaps=[idx[t+1]-idx[t] for t in range(len(idx)-1)]
                        law=sorted({(carry(v0+t,r),gaps[t]) for t in range(len(gaps))})
                        affine = all(g==law[0][1]+ (jj-law[0][0])*(law[1][1]-law[0][1]) for jj,g in law) if len(law)>1 else True
                        found=(side,LAB[want],r,k2,pre2,perm,n,law[:4],affine)
                        break
                if found: break
            if found: break
        if found: break
    if found:
        side,q,r,k,pre,perm,n,law,aff = found
        print('%s  side=%s anchor=%s RADIX=%d digits=%s (%d cells) n=%d lap=%s %s'%(
            m,side,q,r,'/'.join(perm),k,n,law,'AFFINE' if aff else 'non-affine'))
    else:
        print('%s  no consecutive decode found'%m)
