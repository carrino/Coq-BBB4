A,B,C,D=0,1,2,3; S0,S1=0,1
# 1RB1LD_1RC0RB_1LA0RC_0LD0LA
TM={(A,S0):(S1,'R',B),(A,S1):(S1,'L',D),
    (B,S0):(S1,'R',C),(B,S1):(S0,'R',B),
    (C,S0):(S1,'L',A),(C,S1):(S0,'R',C),
    (D,S0):(S0,'L',D),(D,S1):(S0,'L',A)}
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
def rep(u,k): return u*k
# D(j) = 1 (110)^a 0^z 1, head on the rightmost 1, StB.
# left nearest-first = 0^z ++ (011)^a ++ [1]
def Dc(a,z): return (B, ([S0]*z + [S0,S1,S1]*a + [S1], S1, []))
