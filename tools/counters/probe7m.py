# mirror_tm tm_7, tm_7 = 1RB0LC_1LA1RD_1LA1LC_0RD1RB.
# mirror flips dir (L<->R), keeps write+next.  side becomes R, edge A, poff 1, boot [1,1,2,4].
# mirror_tm tm_7 = 1LB0RC_1RA1LD_1RA1RC_0LD1LB
TM = {  # state x sym -> (write, dir(+1=R,-1=L), next)
    (0,0):(1,-1,1), (0,1):(0,+1,2),   # A0=1LB A1=0RC
    (1,0):(1,+1,0), (1,1):(1,-1,3),   # B0=1RA B1=1LD
    (2,0):(1,+1,0), (2,1):(1,+1,2),   # C0=1RA C1=1RC
    (3,0):(0,-1,3), (3,1):(1,-1,1),   # D0=0LD D1=1LB
}
LAB="ABCD"; POFF=1
def chd(l): return l[0] if l else 0
def ctl(l): return l[1:] if l else []
def cstep(c):
    st,(l,h,r)=c; w,d,ns=TM[(st,h)]
    if d==+1: return (ns,([w]+l, chd(r), ctl(r)))
    else:     return (ns,(ctl(l), chd(l), [w]+r))
def show(c):
    st,(l,h,r)=c
    return f"{LAB[st]} [{''.join(str(x) for x in reversed(l))}]({h})[{''.join(str(x) for x in r)}]"
def wbody(front):
    if not front: return [1]
    return [1]*front[0]+[0]+wbody(front[1:])
def carry(po,b):
    if not b: return [] if po else [1]
    if po: return [b[0]+1]+b[1:]
    return [b[0]]+carry(b[0]%2==1,b[1:])
def nextf(poff,f):
    if not f: return []
    return [f[0]+1]+carry((f[0]+poff)%2==1,f[1:])
def Cf(front): return (0,(wbody(front),0,[]))   # edge A=0
def run(front,steps):
    c=Cf(front); hist=[c]
    for _ in range(steps):
        c=cstep(c); hist.append(c)
    return hist
import sys
front=[int(x) for x in sys.argv[1:]] or [4,2,1]
tgt=(0,(wbody(nextf(POFF,front)),0,[]))
print("front",front,"nextf",nextf(POFF,front))
c=Cf(front)
for i in range(40):
    print(f" {i:2d}: {show(c)}", "  <== EVENT" if (c[0]==0 and c[1][2]==[] and i>0 and c[1][0] and c[1][0][0]==1 and c==tgt) else "")
    if c[0]==0 and c==tgt and i>0: print("  reached nextf at step",i); break
    c=cstep(c)
