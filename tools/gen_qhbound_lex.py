#!/usr/bin/env python3
"""Lex-gated census-grade QHBound theorems (UNTRUSTED search).

For wrap-QH residue machines the PLAIN acyclicity liveness gate
rejects (sweep_qhbound_residue.py's qhbound_survivors), search for a
lexicographic liveness certificate over the WRAPPED closure: per
appearing state, bulk_prover.procedure (rules (a)/(b) with the
count-of-1s measures) + lex_check, mirroring Closure.live_lex_ok.
Emits per machine an NgRankE/NgPattE certificate and a theorem closed
by ngram_check_qhbound_lex_sound (theories/Checkers/Wrap.v):

  NonHalt tm /\ QHBound (S t) tm (unfolded) /\ QuasiHaltsSt tm

Usage: gen_qhbound_lex.py SURVIVORS_FILE LIMIT OUT_V
"""
import sys
sys.path.insert(0,'/home/user/Coq-BBB4/tools')
import bulk_prover as bp
import sweep_qhbound_residue as sq
import gen_bulk_certs as gb

def find_lex(m):
    tbl=bp.parse(m)
    tape={};pos=0;q=0;vis=set()
    for _ in range(1024):
        vis.add(q); tr=tbl[(q,tape.get(pos,0))]
        if tr is None: break
        w,d,nq=tr; tape[pos]=w; pos+=1 if d=='R' else -1; q=nq
    for qq in sorted(vis,key=lambda x:(x==0,x)):
        for n in (2,3,4):
            for t in (64,256,1024):
                r=sq.wrapped_closure(tbl,qq,n,t)
                if r is None: continue
                seen,lset,rset,tw=r
                comps_by_state={}
                ok=True
                for qq2 in set(a[0] for a in seen):
                    comps=bp.procedure(tw,n,seen,lset,rset,qq2,
                                       [mm for mm in bp.DEFAULT_MEASURES if bp.meas_ok(mm[0],mm[1],n)])
                    if comps is None: ok=False;break
                    good,_=bp.lex_check(tw,n,seen,lset,rset,qq2,comps)
                    if not good: ok=False;break
                    comps_by_state[qq2]=comps
                if not ok: continue
                # last visit of qq before t
                tp={};p=0;qc=0;s=None
                for i in range(t):
                    if qc==qq: s=i
                    w,d,nq=tbl[(qc,tp.get(p,0))]; tp[p]=w; p+=1 if d=='R' else -1; qc=nq
                if s is None or s>=t: continue
                return qq,s,n,t,seen,lset,rset,comps_by_state
    return None

ms=[l.strip() for l in open(sys.argv[1]) if l.strip()][:int(sys.argv[2])]
chunks=["""From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram Wrap.
Import ListNotations.
"""]
ok=0
for m in ms:
    r=find_lex(m)
    if r is None: continue
    qq,s,n,t,seen,lset,rset,comps_by_state=r
    ok+=1
    name="tm_qlx_%03d"%ok; cname="cert_qlx_%03d"%ok; thm="qlx_%03d"%ok
    fuel=8*len(seen)+64; rounds=len(lset)+len(rset)+4; qs=chr(65+qq)
    per_state=[]
    for qi in range(4):
        comps=comps_by_state.get(qi,[])
        body=("["+";\n   ".join(gb.emit_comp(c) for c in comps)+"]") if comps else "[]"
        per_state.append("  | St%s =>\n  %s"%(chr(65+qi),body))
    chunks.append("""(** %s: quiet %s s=%d; lex-gated QHBound %d (n=%d t=%d, %d ctx) *)

%s

Definition %s (q : St) : list ngcomp :=
  match q with
%s
  end.

Theorem %s :
  NonHalt %s
  /\\ (forall q' s', QuietAfter %s q' s' -> S s' <= S %d)
  /\\ QuasiHaltsSt %s.
Proof.
  apply (ngram_check_qhbound_lex_sound _ St%s %d %d %d %d %d %s).
  vm_compute. reflexivity.
Qed."""%(m,qs,s,t,n,t,len(seen),gb.emit_tm(name,m),cname,"\n".join(per_state),
         thm,name,name,t,name,qs,s,n,t,fuel,rounds,cname))
open(sys.argv[3],'w').write("\n\n".join(chunks)+"\n")
print("emitted",ok)
