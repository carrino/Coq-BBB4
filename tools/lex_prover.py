import sys
sys.setrecursionlimit(1000000)
def parse(m):
    tbl = {}
    for qi, part in enumerate(m.split('_')):
        for si in range(2):
            e = part[3*si:3*si+3]
            tbl[(qi,si)] = None if e=='---' else (int(e[0]), e[1], ord(e[2])-65)
    return tbl
def mirror(tbl):
    return {k:(None if v is None else (v[0],'L' if v[1]=='R' else 'R',v[2])) for k,v in tbl.items()}

def build_closure(tbl, n, t):
    tape={}; pos=0; q=0
    for i in range(t):
        tr=tbl[(q,tape.get(pos,0))]
        if tr is None: return None
        w,d,nq=tr; tape[pos]=w; pos += 1 if d=='R' else -1; q=nq
    minp=min([pos]+list(tape)); maxp=max([pos]+list(tape))
    Lf=lambda i: tape.get(pos-1-i,0); Rf=lambda i: tape.get(pos+1+i,0)
    win=lambda f,d: tuple(f(d+i) for i in range(n))
    depth=max(pos-minp,maxp-pos)+n+2
    lset={win(Lf,d) for d in range(1,depth)}; rset={win(Rf,d) for d in range(1,depth)}
    a0=(q,tape.get(pos,0),win(Lf,0),win(Rf,0))
    for rnd in range(400):
        seen=set(); todo=[a0]
        while todo:
            a=todo.pop()
            if a in seen: continue
            seen.add(a)
            if len(seen)>50000: return None
            q1,s1,lw,rw=a
            tr=tbl[(q1,s1)]
            if tr is None: continue
            w,d,q2=tr
            if d=='R':
                for x in (0,1):
                    rw2=rw[1:]+(x,)
                    if rw2 in rset: todo.append((q2,rw[0],(w,)+lw[:-1],rw2))
            else:
                for x in (0,1):
                    lw2=lw[1:]+(x,)
                    if lw2 in lset: todo.append((q2,lw[0],lw2,(w,)+rw[:-1]))
        newl={a[2] for a in seen if tbl[(a[0],a[1])] and tbl[(a[0],a[1])][1]=='R'}
        newr={a[3] for a in seen if tbl[(a[0],a[1])] and tbl[(a[0],a[1])][1]=='L'}
        if newl<=lset and newr<=rset:
            if any(tbl[(a[0],a[1])] is None for a in seen): return None
            return seen,lset,rset
        lset|=newl; rset|=newr
    return None

def succs(tbl,lset,rset,seen,a):
    q1,s1,lw,rw=a; w,d,q2=tbl[(q1,s1)]
    out=[]
    if d=='R':
        for x in (0,1):
            rw2=rw[1:]+(x,)
            b=(q2,rw[0],(w,)+lw[:-1],rw2)
            if rw2 in rset and b in seen: out.append(b)
    else:
        for x in (0,1):
            lw2=lw[1:]+(x,)
            b=(q2,lw[0],lw2,(w,)+rw[:-1])
            if lw2 in lset and b in seen: out.append(b)
    return out

# measures: 0=whole count1, 1=left count1, 2=right count1; delta of edge (a->b)
def mdelta(tbl,mid,a,b):
    q1,s1,lw,rw=a; w,d,q2=tbl[(q1,s1)]
    if mid==0: return (w==1)-(s1==1)
    if d=='R':
        return (w==1) if mid==1 else -(rw[0]==1)
    else:
        return -(lw[0]==1) if mid==1 else (w==1)

def sccs(nodes,adj):
    # tarjan iterative
    idx={}; low={}; onstk={}; stk=[]; out=[]; c=[0]
    for s in nodes:
        if s in idx: continue
        work=[(s,0)]
        while work:
            v,pi=work[-1]
            if pi==0:
                idx[v]=low[v]=c[0]; c[0]+=1; stk.append(v); onstk[v]=True
            recurse=False
            ns=adj(v)
            for i in range(pi,len(ns)):
                u=ns[i]
                if u not in idx:
                    work[-1]=(v,i+1); work.append((u,0)); recurse=True; break
                elif onstk.get(u): low[v]=min(low[v],idx[u])
            if recurse: continue
            if low[v]==idx[v]:
                comp=[]
                while True:
                    u=stk.pop(); onstk[u]=False; comp.append(u)
                    if u==v: break
                out.append(comp)
            work.pop()
            if work:
                p=work[-1][0]; low[p]=min(low[p],low[v])
    return out

def bellman_potentials(nodes,edges,w):
    # find phi with w(e) <= phi[u] - phi[v] - 1 for all edges (u->v)? we want every cycle strictly negative in delta
    # potentials: longest-path style on weights W(e)=K*delta+1 <= phi[u]-phi[v] i.e. phi[v] <= phi[u]-W(e)
    # feasible iff no cycle with sum W > 0... use Bellman-Ford on -W
    INF=float('inf'); dist={v:0 for v in nodes}
    for _ in range(len(nodes)+1):
        ch=False
        for (u,v,We) in edges:
            if dist[u]-We < dist[v]:
                dist[v]=dist[u]-We; ch=True
        if not ch:
            mn=min(dist.values())
            return {v:int(dist[v]-mn) for v in nodes}
    return None

def procedure(tbl,seen,lset,rset,qq,K=None):
    # graph: q-avoiding edges among q-avoiding nodes... edges into q-nodes exempt.
    nodes=[a for a in seen if a[0]!=qq]
    Kc = len(nodes)+2
    alive={}  # edge set
    for a in nodes:
        for b in succs(tbl,lset,rset,seen,a):
            if b[0]!=qq: alive[(a,b)]=True
    comps=[]  # lex components emitted
    rounds=0
    while True:
        rounds+=1
        if rounds>200: return None
        adj=lambda v:[b for (u,b) in alive if u==v]  # slow but fine
        adjmap={}
        for (u,v) in alive: adjmap.setdefault(u,[]).append(v)
        adj=lambda v: adjmap.get(v,[])
        comp_list=sccs(nodes,adj)
        cyclic=[c for c in comp_list if len(c)>1 or (c[0] in adjmap and c[0] in adjmap.get(c[0],[]))]
        if not cyclic:
            # emit final rank: topological rank on remaining graph (longest path)
            rank={v:0 for v in nodes}
            for _ in range(len(nodes)+1):
                ch=False
                for (u,v) in alive:
                    if rank[u] < rank[v]+1: rank[u]=rank[v]+1; ch=True
                if not ch: break
            comps.append(("rank",rank))
            return comps
        # emit condensation rank (decreases on inter-scc edges, ties intra)
        cidx={}
        for i,c in enumerate(comp_list):
            for v in c: cidx[v]=i
        # topo order of sccs: rank via longest path on condensation
    # (emit once per round)
        crank={i:0 for i in range(len(comp_list))}
        for _ in range(len(comp_list)+1):
            ch=False
            for (u,v) in alive:
                if cidx[u]!=cidx[v] and crank[cidx[u]] < crank[cidx[v]]+1:
                    crank[cidx[u]]=crank[cidx[v]]+1; ch=True
            if not ch: break
        comps.append(("rank",{v:crank[cidx[v]] for v in nodes}))
        progress=False
        for c in cyclic:
            cs=set(c)
            intra=[(u,v) for (u,v) in alive if u in cs and v in cs]
            # rule (a): measure nonincreasing on all intra, strict on some
            done=False
            for mid in (0,1,2):
                ds={e:mdelta(tbl,mid,*e) for e in intra}
                if all(d<=0 for d in ds.values()) and any(d<0 for d in ds.values()):
                    comps.append(("meas",mid,1,{v:0 for v in c},cs))  # K=1, phi=0, gate=cs
                    for e in intra:
                        if ds[e]<0: del alive[e]
                    progress=True; done=True; break
            if done: continue
            # rule (b): every cycle strictly decreases some measure: potentials
            for mid in (0,1,2):
                W=[(u,v,Kc*mdelta(tbl,mid,u,v)+1) for (u,v) in intra]
                phi=bellman_potentials(list(cs),W,None)
                if phi is not None:
                    comps.append(("meas",mid,Kc,phi,cs))
                    for e in intra: del alive[e]
                    progress=True; break
        if not progress: return None

def lex_check(tbl,seen,lset,rset,qq,comps,Kc):
    ok=True
    for a in seen:
        if a[0]==qq: continue
        for b in succs(tbl,lset,rset,seen,a):
            if b[0]==qq: continue
            good=False
            for comp in comps:
                if comp[0]=="rank":
                    r=comp[1]
                    if r.get(b,0) < r.get(a,0): good=True; break
                    if r.get(b,0) <= r.get(a,0): continue
                    break
                else:
                    _,mid,K,phi,gate=comp
                    d=mdelta(tbl,mid,a,b)
                    ga=a in gate; gb=b in gate
                    if ga and gb:
                        v=K*d+phi.get(b,0)-phi.get(a,0)
                        if v<=-1: good=True; break
                        if v<=0: continue
                        break
                    if not gb: continue   # value drops to 0: nonincrease
                    break                  # not ga, gb: unbounded increase
            if not good:
                return False,(a,b)
    return True,None

def run(name,tbl,n,t):
    r=build_closure(tbl,n,t)
    if r is None: print(name,n,"no closure"); return
    seen,lset,rset=r
    states={a[0] for a in seen}
    allok=True; total=0
    for qq in sorted(states):
        comps=procedure(tbl,seen,lset,rset,qq)
        if comps is None: print(name,f"n={n} q={chr(65+qq)}: procedure FAILED"); allok=False; continue
        ok,bad=lex_check(tbl,seen,lset,rset,qq,comps,len(seen)+2)
        total+=len(comps)
        if not ok: print(name,f"n={n} q={chr(65+qq)}: LEX CHECK FAILED on",bad); allok=False
    if allok: print(name,f"n={n}: ALL STATES PASS, {len(seen)} ctxs, {total} components total")

sample=mirror(parse("1RB1LD_1LC0LD_1RC1RA_0LB0RA"))
for nn in (2,3,4):
    run("sample",sample,nn,0)
