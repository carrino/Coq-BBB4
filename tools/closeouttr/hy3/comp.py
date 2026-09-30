"""run-length compression of a tape string (HY3 viewers)"""
def comp(s, minrep=4):
    # s: string of symbols (may include [X] head markers kept as single tokens)
    toks=[]; i=0
    while i<len(s):
        if s[i]=='[': j=s.index(']',i); toks.append(s[i:j+1]); i=j+1
        else: toks.append(s[i]); i+=1
    out=[]; i=0; n=len(toks)
    while i<n:
        best=None
        for u in range(1,7):
            if i+u>n: break
            unit=toks[i:i+u]
            if any(t.startswith('[') for t in unit): break
            k=1
            while toks[i+k*u:i+(k+1)*u]==unit: k+=1
            if k>=minrep and (best is None or k*u>best[0]*best[1]): best=(k,u)
        if best:
            k,u=best; out.append('('+''.join(toks[i:i+u])+')^%d'%k); i+=k*u
        else: out.append(toks[i]); i+=1
    return ' '.join(x for x in out)
