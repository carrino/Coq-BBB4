#!/usr/bin/env python3
"""UNTRUSTED NGramHist prover + Coq emitter (wave-6).

Mirrors theories/Checkers/NGramHist.v EXACTLY:
 - augmented step hcstep (cell = (bit, last-k (state,read)) records);
 - head-relative n-gram closure hng_succs (gram sets = lists of hsym windows,
   far cell branched over set completions with prefix match);
 - hctx_enc (the positive node key) for the phase-dependent lex cert.
The Coq kernel re-checks every emitted certificate via vm_compute; this tool
only transcribes.  States A..D, symbols 0/1.
"""
import sys

# ---------------- machine ----------------
def decode(mstr):
    g = mstr.strip().split('_'); assert len(g)==4
    tm={}
    for si,grp in enumerate(g):
        st="ABCD"[si]; tm[st]={}
        for b in (0,1):
            c=grp[b*3:b*3+3]
            tm[st][b]=None if c=='---' else (int(c[0]),c[1],c[2])
    return tm

# ---------------- augmented alphabet ----------------
# hsym = (bit, tuple of (state_char, bit)) ; blank = (0, ())
BLANK=(0,())
def bit(x): return x[0]

def make_step(tm,k):
    def step(s,sym):
        i0,i1=sym
        tr=tm[s][i0]
        if tr is None: return None
        w,d,nx=tr
        return (nx,d,(w, (( (s,i0), )+i1)[:k]))
    return step

# ---------------- concrete augmented simulation (seed at step t) ----------------
def simulate(tm,k,t):
    step=make_step(tm,k)
    left={};right={};head=BLANK;s='A'
    for _ in range(t):
        tr=step(s,head)
        if tr is None: return None
        nx,d,w=tr
        if d=='R':
            nl={0:w}
            for i,v in left.items(): nl[i+1]=v
            left=nl; head=right.get(0,BLANK)
            right={j-1:v for j,v in right.items() if j>=1}
        else:
            nr={0:w}
            for j,v in right.items(): nr[j+1]=v
            right=nr; head=left.get(0,BLANK)
            left={i-1:v for i,v in left.items() if i>=1}
        s=nx
    Lmax=max(left) if left else -1; Rmax=max(right) if right else -1
    L=[left.get(i,BLANK) for i in range(Lmax+1)]
    R=[right.get(j,BLANK) for j in range(Rmax+1)]
    return (s,L,head,R)

def hnthb(l,i): return l[i] if i<len(l) else BLANK
def hwin(l,d,n): return tuple(hnthb(l,d+i) for i in range(n))

def seed(tm,k,n,t):
    cfg=simulate(tm,k,t)
    if cfg is None: return None
    s,L,head,R=cfg
    a0=(s,(hwin(L,0,n),head,hwin(R,0,n)))
    lset=set(); rset=set()
    for d in range(1,len(L)+2): lset.add(hwin(L,d,n))
    for d in range(1,len(R)+2): rset.add(hwin(R,d,n))
    return a0,lset,rset

# ---------------- hng_succs (mirrors Coq) ----------------
def hng_succs(tm,k,n,lset,rset,a):
    q,(lw,s,rw)=a
    tr=tm[q][bit(s)]
    if tr is None: return None
    w=(tr[0], (((q,bit(s)),)+s[1])[:k])
    d=tr[1]; nx=tr[2]
    if d=='R':
        if lw not in lset: return None
        out=[]
        hchd_rw = rw[0] if rw else BLANK
        for g in rset:
            if len(g)==n and g[:n-1]==rw[1:]:
                out.append((nx,((w,)+lw[:-1], hchd_rw, g)))
        return out
    else:
        if rw not in rset: return None
        out=[]
        hchd_lw = lw[0] if lw else BLANK
        for g in lset:
            if len(g)==n and g[:n-1]==lw[1:]:
                out.append((nx,(g, hchd_lw, (w,)+rw[:-1])))
        return out

MAXNODES=2500

def explore(tm,k,n,a0,lset,rset,fuel):
    seen=set([a0]); todo=[a0]; steps=0
    while todo:
        steps+=1
        if steps>fuel or len(seen)>MAXNODES: return None
        a=todo.pop()
        sc=hng_succs(tm,k,n,lset,rset,a)
        if sc is None: continue          # stuck: donation feeds next round
        for b in sc:
            if b not in seen: seen.add(b); todo.append(b)
    return seen

def grow(tm,k,n,t,fuel,rounds=150):
    sd=seed(tm,k,n,t)
    if sd is None: return None
    a0,lset,rset=sd
    for _ in range(rounds):
        seen=explore(tm,k,n,a0,lset,rset,fuel)
        if seen is None: return None
        dl=set(); dr=set()
        for a in seen:
            q,(lw,s,rw)=a; tr=tm[q][bit(s)]
            if tr is None: continue
            if tr[1]=='R': dl.add(lw)
            else: dr.add(rw)
        nl=lset|dl; nr=rset|dr
        if nl==lset and nr==rset:
            # verify closed: every node's succs in seen (with final sets)
            edges={}
            for a in seen:
                sc=hng_succs(tm,k,n,lset,rset,a)
                if sc is None: return None   # stuck under final sets -> not closed
                if any(b not in seen for b in sc): return None
                edges[a]=sc
            return a0,lset,rset,seen,edges
        lset,rset=nl,nr
    return None

# ---------------- lex cert (phase-dependent count measures) ----------------
def zc(sym): return 1 if bit(sym)==1 else 0
def ngm_delta(tm,meas,a):
    q,(lw,s,rw)=a; tr=tm[q][bit(s)]
    if tr is None: return 0
    w,d,nx=tr; zw=1 if w==1 else 0; zs=zc(s)
    if meas=='All': return zw-zs
    if meas=='Left': return zw if d=='R' else -zc(lw[0] if lw else BLANK)
    if meas=='Right': return (-zc(rw[0] if rw else BLANK)) if d=='R' else zw
    return 0

def bellman_phi(nodes, edges_w, K):
    """Solve phi(b) - phi(a) <= -1 - K*w(a->b) for all edges; return dict phi>=0
    (nats) or None if infeasible (positive cycle w.r.t. the strict system)."""
    idx={a:i for i,a in enumerate(nodes)}
    d={a:0 for a in nodes}
    N=len(nodes)
    for it in range(N+1):
        changed=False
        for (a,b,w) in edges_w:
            nv=d[a]+(-1-K*w)
            if nv<d[b]:
                d[b]=nv; changed=True
                if it==N: return None    # negative cycle -> infeasible
        if not changed: break
    mn=min(d.values()) if d else 0
    return {a:d[a]-mn for a in nodes}

def try_rank(nodes, adj):
    """If the subgraph is acyclic, return a longest-path rank potential
    (phi strictly decreases along every edge); else None."""
    col={a:0 for a in nodes}; order=[]
    for start in nodes:
        if col[start]: continue
        stack=[(start,iter(adj[start]))]; col[start]=1
        while stack:
            node,it=stack[-1]; adv=False
            for nb in it:
                c=col[nb]
                if c==1: return None      # back-edge => cycle
                if c==0:
                    col[nb]=1; stack.append((nb,iter(adj[nb]))); adv=True; break
            if not adv:
                col[node]=2; order.append(node); stack.pop()
    phi={}
    for a in order:  # post-order: successors resolved first
        phi[a]=0 if not adj[a] else 1+max(phi[b] for b in adj[a])
    return phi

def cert_for_state(tm,seen,edges,q,K=None):
    """Return a list of hcomp for state q (as python dicts) or None.
    Tries a plain rank (acyclic) first -- HRank works for lex_ok and
    live_lex_ok -- then single count measures with Bellman-Ford potentials."""
    nodes=[a for a in seen if a[0]!=q]
    if not nodes: return []              # q-avoiding subgraph empty
    nodeset=set(nodes)
    adj={a:[b for b in edges[a] if b in nodeset] for a in nodes}
    rk=try_rank(nodes,adj)
    if rk is not None:
        return [('HRank',rk)]
    if K is None: K=len(seen)+2
    for meas in ('Left','Right','All'):
        ew=[(a,b,ngm_delta(tm,meas,a)) for a in nodes for b in adj[a]]
        phi=bellman_phi(nodes,ew,K)
        if phi is not None:
            return [('HMeas',meas,K,phi,set(nodes))]
    return None

def visited_states_prefix(tm,k,t):
    """States visited in steps [0,t) from blank.  The never-QH obligation
    covers these too: a prefix-visited state that does NOT recur is quiet ->
    the machine QUASIHALTS (not never-QH).  Missing this is the safety!=
    liveness trap."""
    step=make_step(tm,k); left={};right={};head=BLANK;s='A'; vis=set()
    for _ in range(t):
        vis.add(s); tr=step(s,head)
        if tr is None: break
        nx,d,w=tr
        if d=='R':
            nl={0:w}
            for i,v in left.items(): nl[i+1]=v
            left=nl; head=right.get(0,BLANK); right={j-1:v for j,v in right.items() if j>=1}
        else:
            nr={0:w}
            for j,v in right.items(): nr[j+1]=v
            right=nr; head=left.get(0,BLANK); left={i-1:v for i,v in left.items() if i>=1}
        s=nx
    vis.add(s); return vis

def prove(mstr,k,n,t,fuel):
    tm=decode(mstr)
    g=grow(tm,k,n,t,fuel)
    if g is None: return None
    a0,lset,rset,seen,edges=g
    appearing=set(a[0] for a in seen)
    # never-QH obligation: EVERY state visited-in-prefix OR appearing needs a
    # liveness cert.  A prefix-only state -> q-avoiding subgraph = whole
    # closure -> cert_for_state fails -> reject (correctly, it's a quasihalter).
    obliged = appearing | visited_states_prefix(tm,k,t)
    cert={}
    for q in 'ABCD':
        if q in obliged:
            c=cert_for_state(tm,seen,edges,q)
            if c is None: return None    # liveness not discharged -> not never-QH
            cert[q]=c
        else:
            cert[q]=[]
    return dict(tm=tm,k=k,n=n,t=t,fuel=fuel,lset=lset,rset=rset,
               seen=seen,edges=edges,cert=cert,nctx=len(seen))

# ---------------- hctx_enc (positive key, mirrors Coq) ----------------
def st_app(q,p):
    return {'A':4*p,'B':4*p+1,'C':4*p+2,'D':4*p+3}[q]
def sym_app(b,p): return 2*p if b==0 else 2*p+1
def hpair_app(x,p): return st_app(x[0], sym_app(x[1], p))
def hrec_app(l,p):
    if not l: return 2*p
    return 2*hpair_app(l[0],hrec_app(l[1:],p))+1
def hsym_app(x,p): return sym_app(x[0], hrec_app(list(x[1]),p))
def hsyms_app(l,p):
    if not l: return 2*p
    return 2*hsym_app(l[0],hsyms_app(l[1:],p))+1
def hctx_enc(a):
    q,(lw,s,rw)=a
    return st_app(q, hsym_app(s, hsyms_app(list(lw), hsyms_app(list(rw), 1))))

# ---------------- Coq emitter ----------------
def c_sym(b): return 'S1' if b==1 else 'S0'
def c_st(q): return 'St'+q
def c_hrec(l): return '['+';'.join('({},{})'.format(c_st(x[0]),c_sym(x[1])) for x in l)+']'
def c_hsym(x): return '({},{})'.format(c_sym(x[0]), c_hrec(list(x[1])))
def c_win(g): return '['+';'.join(c_hsym(x) for x in g)+']'
def c_gset(s): return '['+';\n   '.join(c_win(g) for g in sorted(s))+']'
def c_tm(tm,name):
    arms=[]
    for q in 'ABCD':
        for b in (0,1):
            tr=tm[q][b]
            rhs='None' if tr is None else 'Some (mkTrans {} {} {})'.format(
                c_sym(tr[0]), 'DR' if tr[1]=='R' else 'DL', c_st(tr[2]))
            arms.append('  | {}, {} => {}'.format(c_st(q),c_sym(b),rhs))
    return 'Definition {} : TM := fun q s =>\n  match q, s with\n{}\n  end.'.format(
        name,'\n'.join(arms))
def c_cert(cert,name):
    arms=[]
    for q in 'ABCD':
        comps=[]
        for c in cert[q]:
            if c[0]=='HMeas':
                _,meas,K,phi,gate=c
                meas_c={'All':'MAll','Left':'MLeft','Right':'MRight'}[meas]
                phil='['+';'.join('({}%positive,{})'.format(hctx_enc(a),v)
                                  for a,v in phi.items())+']'
                gatel='['+';'.join('{}%positive'.format(hctx_enc(a)) for a in gate)+']'
                comps.append('HMeas {} {} {} {}'.format(meas_c,K,phil,gatel))
            elif c[0]=='HRank':
                _,phi=c
                phil='['+';'.join('({}%positive,{})'.format(hctx_enc(a),v)
                                  for a,v in phi.items())+']'
                comps.append('HRank {}'.format(phil))
        arms.append('  | {} => [{}]'.format(c_st(q),'; '.join(comps)))
    return 'Definition {} (q:St) : list hcomp :=\n  match q with\n{}\n  end.'.format(
        name,'\n'.join(arms))

def emit(mstr,res,idx=0):
    nm='%05d'%idx
    tm=res['tm']
    thm='nqh_h_'+nm
    body=[]
    body.append(c_tm(tm,'tm_h_'+nm))
    body.append('Definition lset_h_'+nm+' : hgset :=\n  '+c_gset(res['lset'])+'.')
    body.append('Definition rset_h_'+nm+' : hgset :=\n  '+c_gset(res['rset'])+'.')
    body.append(c_cert(res['cert'],'cert_h_'+nm))
    body.append(
      'Theorem {thm} : NeverQuasiHaltsSt tm_h_{nm}.\n'
      'Proof.\n'
      '  apply (ngramhist_check_neverqh_lex_sound tm_h_{nm} {k} {n} {t} {fuel}\n'
      '           lset_h_{nm} rset_h_{nm} cert_h_{nm}).\n'
      '  vm_compute. reflexivity.\nQed.'.format(
        thm=thm,nm=nm,k=res['k'],n=res['n'],t=res['t'],fuel=res['fuel']))
    return '\n\n'.join(body), thm

HEADER='''(* UNTRUSTED-generated; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist.
Import ListNotations.
'''

if __name__=='__main__':
    m=sys.argv[1]; k=int(sys.argv[2]); n=int(sys.argv[3]); t=int(sys.argv[4]); fuel=int(sys.argv[5])
    res=prove(m,k,n,t,fuel)
    if res is None:
        print('(* PROVER FAILED for '+m+' *)'); sys.exit(2)
    body,thm=emit(m,res)
    out=sys.argv[6] if len(sys.argv)>6 else '/dev/stdout'
    with open(out,'w') as f:
        f.write(HEADER+'\n'+body+'\n')
    sys.stderr.write('OK {} nctx={} -> {}\n'.format(m,res['nctx'],out))

# ================= QHBound / wrap harvest (R_QH tier) =================
def wrap_tm(tm,q):
    """tm_wrap: redirect state q to halt (None)."""
    w={}
    for st in 'ABCD':
        w[st]={}
        for b in (0,1):
            w[st][b]=None if st==q else tm[st][b]
    return w

def grow_wrap(ctm, seed_tm, k, n, t, fuel, rounds=150):
    """Grow the closure of ctm, seeded from seed_tm's step-t config."""
    sd=seed(seed_tm,k,n,t)
    if sd is None: return None
    a0,lset,rset=sd
    for _ in range(rounds):
        seen=explore(ctm,k,n,a0,lset,rset,fuel)
        if seen is None: return None
        dl=set(); dr=set()
        for a in seen:
            q2,(lw,s,rw)=a; tr=ctm[q2][bit(s)]
            if tr is None: continue
            if tr[1]=='R': dl.add(lw)
            else: dr.add(rw)
        nl=lset|dl; nr=rset|dr
        if nl==lset and nr==rset:
            edges={}
            for a in seen:
                sc=hng_succs(ctm,k,n,lset,rset,a)
                if sc is None: return None
                if any(b not in seen for b in sc): return None
                edges[a]=sc
            return a0,lset,rset,seen,edges
        lset,rset=nl,nr
    return None

def last_visits(tm,k,T=4000):
    """last step each state is visited (from blank), or None if halts."""
    step=make_step(tm,k); left={};right={};head=BLANK;s='A'; last={}
    for i in range(T):
        last[s]=i; tr=step(s,head)
        if tr is None: return None,last
        nx,d,w=tr
        if d=='R':
            nl={0:w}
            for j,v in left.items(): nl[j+1]=v
            left=nl; head=right.get(0,BLANK); right={j-1:v for j,v in right.items() if j>=1}
        else:
            nr={0:w}
            for j,v in right.items(): nr[j+1]=v
            right=nr; head=left.get(0,BLANK); left={j-1:v for j,v in left.items() if j>=1}
        s=nx
    last[s]=T; return T,last

def prove_qh(mstr,k,n,fuel,tmax=1900):
    """Prove the R_QH triple via the wrap variant for some quiet state q.
    Returns dict(...,q,s,t,...) or None."""
    tm=decode(mstr)
    halted,last=last_visits(tm,k)
    if halted is None: return None          # HALTS within T -> not our tier
    # candidate quiet states: last visit < tmax, sorted by last-visit
    cands=sorted((q for q in 'ABCD' if q in last), key=lambda q: last[q])
    for q in cands:
        s=last[q]
        if s>=tmax: continue
        t=min(s+25, tmax)
        if not (s<t): continue
        tmw=wrap_tm(tm,q)
        g=grow_wrap(tmw,tm,k,n,t,fuel)
        if g is None: continue
        a0,lset,rset,seen,edges=g
        appearing=set(a[0] for a in seen)
        if q in appearing: continue          # q must be quiet (not recur)
        cert={}; ok=True
        for q2 in 'ABCD':
            if q2 in appearing:
                c=cert_for_state(tmw,seen,edges,q2)
                if c is None: ok=False; break
                cert[q2]=c
            else: cert[q2]=[]
        if not ok: continue
        return dict(tm=tm,tmw=tmw,q=q,s=s,k=k,n=n,t=t,fuel=fuel,
                    lset=lset,rset=rset,seen=seen,edges=edges,cert=cert,nctx=len(seen))
    return None

def emit_qh(mstr,res,idx=0):
    nm='%05d'%idx; tm=res['tm']
    thm='cqh_h_'+nm
    body=[]
    body.append(c_tm(tm,'tmq_h_'+nm))
    body.append('Definition lsetq_h_'+nm+' : hgset :=\n  '+c_gset(res['lset'])+'.')
    body.append('Definition rsetq_h_'+nm+' : hgset :=\n  '+c_gset(res['rset'])+'.')
    body.append(c_cert(res['cert'],'certq_h_'+nm))
    body.append(
      'Lemma {thm} : iqh tmq_h_{nm}.\n'
      'Proof.\n'
      '  unfold iqh.\n'
      '  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_{nm} {q} {s} {k} {n} {t} {fuel}\n'
      '                lsetq_h_{nm} rsetq_h_{nm} certq_h_{nm} ltac:(vm_compute; reflexivity))\n'
      '    as (Hnh & Hb & Hqh).\n'
      '  split; [exact Hnh | split;\n'
      '    [ apply (qhbound_mono (S {t}) 2000 tmq_h_{nm}); [lia | exact Hb] | exact Hqh ] ].\nQed.'.format(
        thm=thm,nm=nm,q=c_st(res['q']),s=res['s'],k=res['k'],n=res['n'],t=res['t'],fuel=res['fuel']))
    return '\n\n'.join(body), thm, 'tmq_h_'+nm

HEADER_QH='''(* UNTRUSTED-generated R_QH tier; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist NGramHistWrap.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.
'''
