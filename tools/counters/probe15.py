A,B,C,D=0,1,2,3; S0,S1=0,1
# 1RB0RC_0LC1LB_0LD1LC_1RD0RA  (wave4 #15)
TM={(A,S0):(S1,'R',B),(A,S1):(S0,'R',C),
    (B,S0):(S0,'L',C),(B,S1):(S1,'L',B),
    (C,S0):(S0,'L',D),(C,S1):(S1,'L',C),
    (D,S0):(S1,'R',D),(D,S1):(S0,'R',A)}
def chd(l): return l[0] if l else S0
def ctl(l): return l[1:] if l else []
def cstep(c):
    q,(L,h,R)=c; tr=TM.get((q,h))
    if tr is None: return None
    w,d,nq=tr
    return (nq,([w]+L,chd(R),ctl(R))) if d=='R' else (nq,(ctl(L),chd(L),[w]+R))
def csteps(n,c):
    for _ in range(n):
        c=cstep(c)
        if c is None: return None
    return c
c0=(A,([],S0,[]))
