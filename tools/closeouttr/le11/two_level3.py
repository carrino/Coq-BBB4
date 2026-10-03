# LE11 (untrusted): the abstract macro step of the two-level mirror counters (SCOPING_INSTR 7.4.LE11).
def binc(x):
    x=list(x); i=0
    while i<len(x) and x[i]==1: x[i]=0; i+=1
    if i<len(x): x[i]=1
    else: x.append(1)
    return x
def allt(l): return all(l)
def step(s):
    p,u,v,y=s
    if not allt(y):
        y1=binc(y)
        if not allt(u): return (p,binc(u),v,y1),'n'
        k=len(u)
        if p=='P1':
            if not v: return ('P1',[0]*(k+1),[],y1),'top1'
            if v[0]==0: return ('P1',[0]*(k+1),v[1:],y1),'abs0'
            if k%2==0: return ('P2',[],v[1:],[1]*(3*k//2)+[0]+y1),'abs1e'
            return ('P1',[],v[1:],[0]*((3*k+1)//2)+[1]+y1),'abs1o'
        else:
            if not v: return ('P1',[0]*(k+1),[],y1),'top2'
            if v[0]==0: return ('P2',[0]*(k+1),v[1:],y1),'abs0'
            if k%2==1: return ('P2',[],v[1:],[0]*((3*k+1)//2)+[1]+y1),'abs1o2'
            b=binc(v[1:])
            return ('P1',[0]+b[:-1],[],[0]*(3*k//2)+[1]+y1),'abs1e2'
    assert p=='P1' and not v, ('bad ovf',s)
    w=len(y)
    if not u: return ('P1',[],[],[0]*(w+1)),'ovfE'
    if u[0]==1: return ('P2',[],u[1:]+[1],[0]*(w+1)),'ovf1'
    return ('P1',[0],u[1:]+[1],[0]*w),'ovf0'
def cells(s):
    p,u,v,y=s
    xc=lambda l:''.join('100' if b else '000' for b in l)
    L=xc(u)+('1' if p=='P1' else '10')+xc(v)
    R=''.join('11' if b else '10' for b in y)+'11'
    return L.rstrip('0'),R
