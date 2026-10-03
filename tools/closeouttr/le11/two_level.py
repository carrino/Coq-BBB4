# LE11 (untrusted): the abstract macro step of the two-level mirror counters (SCOPING_INSTR 7.4.LE11).
# abstract model S(u,v,y) for 1RB1LD_1RC0RB_1LA1RC_1LA0LA
def binc(x):
    x=list(x); i=0
    while i<len(x) and x[i]==1: x[i]=0; i+=1
    if i<len(x): x[i]=1
    else: x.append(1)
    return x
def step(u,v,y):
    if 0 in y:
        y2=binc(y)
        if 0 in u: return binc(u),v,y2,'n'
        k=len(u)
        if not v: return [0]*(k+1),[],y2,'top'   # left top carry (era)
        if v[0]==1: return [],v[1:],[1]*k+[0]+y2,'abs1'
        return [0]*(k+1),v[1:],y2,'abs0'
    # overflow
    w=len(y)
    if not u and not v: return [],[],[0]*(w+1),'ovfE'
    assert u, ('ovf u empty',u,v,y)
    if u[0]==1: return [],u[1:]+[1]+v,[0]*(w+1),'ovf1'
    return [0],u[1:]+[1]+v,[0]*w,'ovf0'
def cells(u,v,y):
    L=''.join('10' if b else '00' for b in u)+'1'+''.join('10' if b else '00' for b in v)
    R=''.join('11' if b else '10' for b in y)+'11'
    return L.rstrip('0'),R
