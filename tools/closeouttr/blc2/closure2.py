"""BLC2 closure test (UNTRUSTED, SCOPING_INSTR.md 7.4.BLC2): is the k-gram language of the
digits of 0RB1RB_1LC1RA_1RA0LD_1LC1LD (learned from the C0 snapshots) closed under one round?

    cd tools/closeouttr/blc2 && python3 closure2.py 0RB1RB_1LC1RA_1RA0LD_1LC1LD K NTRIALS
"""
import sys,re,random,collections
from sim import parse, run
spec=sys.argv[1]; K=int(sys.argv[2]); NT=int(sys.argv[3])
tab=parse(spec)
# real snapshots at C0
snaps=[]
for t,q,h,s in run(spec,3000000,show=lambda t,q,h,pos,tape:(q,h)==(2,0)):
    bl=[len(m.group()) for m in re.finditer(r'1{3,}',s)]
    snaps.append(bl)
def digs(bl): return [bl[i]-2*bl[i+1] for i in range(len(bl)-1)]
# strings read from the far end: reversed digits, with a start marker
grams=set()
for bl in snaps:
    d=['^']*(K-1)+digs(bl)[::-1]
    for i in range(len(d)-K+1): grams.add(tuple(d[i:i+K]))
print('grams',len(grams))
tailreal=snaps[-1][-3:]   # far end kept
def round_(bl):
    s='00'+'0'.join('1'*b for b in bl)+'011'
    tape={i:int(c) for i,c in enumerate(s)}; pos=0; q=2
    for t in range(10**6):
        h=tape.get(pos,0)
        if t>0 and (q,h)==(2,0): break
        w,d,nq=tab[(q,h)]; tape[pos]=w; pos+=d; q=nq
    lo=min(tape);hi=max(tape); s=''.join(str(tape.get(i,0)) for i in range(lo,hi+1))
    return [len(m.group()) for m in re.finditer(r'1{3,}',s)]
def ok(bl):
    d=['^']*(K-1)+digs(bl)[::-1]
    return all(tuple(d[i:i+K]) in grams for i in range(len(d)-K+1))
random.seed(2); good=bad=0; ex=[]
base=digs(tailreal)[::-1]
for trial in range(NT):
    n=random.randint(2,7)
    d=['^']*(K-1)+base
    for i in range(n):
        c=[g[-1] for g in grams if list(g[:-1])==d[len(d)-K+1:]]
        if not c: break
        d.append(random.choice(c))
    bl=list(tailreal)
    for x in d[K-1+len(base):]: bl.insert(0,2*bl[0]+x)
    if min(bl)<1: continue
    nb=round_(bl)
    if ok(nb): good+=1
    else:
        bad+=1
        if len(ex)<4: ex.append((bl,digs(bl),nb,digs(nb)))
print('K',K,'closed',good,'not',bad)
for e in ex: print(e)
