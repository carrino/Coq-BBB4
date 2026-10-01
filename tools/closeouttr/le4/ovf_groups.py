import re,sys,os,collections
def prim(u):
    n=len(u)
    for d in range(1,n+1):
        if n%d==0 and u[:d]*(n//d)==u: return u[:d]
def rle(s, minrep=3):
    out=[];i=0;n=len(s)
    while i<n:
        best=None
        for k in range(1,5):
            u=s[i:i+k]
            if len(u)<k or prim(u)!=u or not u.isdigit(): continue
            j=i
            while s[j:j+k]==u: j+=k
            r=(j-i)//k
            if r>=minrep and (best is None or r*k>best[1]*len(best[0])): best=(u,r)
        if best: out.append((best[0],best[1])); i+=len(best[0])*best[1]
        else: out.append((s[i],1)); i+=1
    # merge literals
    res=[];lit=''
    for u,r in out:
        if r==1: lit+=u
        else:
            if lit: res.append(lit); lit=''
            res.append('(%s)^%d'%(u,r))
    if lit: res.append(lit)
    return res
def shape(tok): return [re.sub(r'\^\d+','^n',t) for t in tok]
if __name__=='__main__':
    D=sys.argv[1]
    G=collections.defaultdict(list)
    for f in sorted(os.listdir(D)):
        L=open(os.path.join(D,f)).read().split('\n')
        L=[l.split() for l in L if l.strip() and not l.startswith(('HALT','OUT'))]
        if not L: G['none'].append(f[:-4]);continue
        # last overflow per side
        last={}
        for t,sd,tp in L: last[sd]=tp
        sides=''.join(sorted(last))
        nblk=max(sum(1 for t in rle(tp) if '^' in t) for tp in last.values())
        G[(sides,nblk)].append(f[:-4])
    for k,v in sorted(G.items(),key=lambda kv:-len(kv[1])): print(k,len(v),v[:3])
