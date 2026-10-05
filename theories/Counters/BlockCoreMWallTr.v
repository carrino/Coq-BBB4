(** * A protected right guard forcing B1 in the M block-list core.

    The six-state automaton admits D with right word 0001101111 and
    arbitrary finite left word. Every step avoiding B1 preserves it,
    and an empty right word forces B1. The finite macros connect the
    two marked frontier prefixes to this guard in 19 and 29 steps.

    The automaton is reproduced by block_core_m_frontier.py and its
    local closure is checked exhaustively in Coq.
*)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreMReturnTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
(* BEGIN GENERATED FINITE CERTIFICATE *)
Inductive mw_state:=W0|W1|W2|W3|W4|W5.
Definition mw_cons(a:Sym)(s:mw_state):mw_state:=match a,s with
|S0,W0=>W1|S1,W0=>W2
|S0,W1=>W1|S1,W1=>W2
|S0,W2=>W3|S1,W2=>W2
|S0,W3=>W4|S1,W3=>W5
|S0,W4=>W2|S1,W4=>W2
|S0,W5=>W5|S1,W5=>W5
end.
Fixpoint mw_fold(R:list Sym):mw_state:=match R with []=>W0|a::R=>mw_cons a(mw_fold R)end.
Definition mw_ok(q:St)(h:Sym)(s:mw_state):bool:=match q,h,s with
|StA,S0,W0=>false
|StA,S1,W0=>false
|StB,S0,W0=>false
|StC,S0,W0=>false
|StC,S1,W0=>false
|StD,S0,W0=>false
|StD,S1,W0=>false
|StA,S0,W1=>false
|StA,S1,W1=>false
|StB,S0,W1=>false
|StC,S0,W1=>false
|StC,S1,W1=>false
|StD,S0,W1=>false
|StD,S1,W1=>false
|StA,S0,W2=>true
|StA,S1,W2=>false
|StB,S0,W2=>false
|StC,S0,W2=>false
|StC,S1,W2=>false
|StD,S0,W2=>false
|StD,S1,W2=>false
|StA,S0,W3=>false
|StA,S1,W3=>true
|StB,S0,W3=>false
|StC,S0,W3=>true
|StC,S1,W3=>true
|StD,S0,W3=>true
|StD,S1,W3=>false
|StA,S0,W4=>false
|StA,S1,W4=>false
|StB,S0,W4=>true
|StC,S0,W4=>false
|StC,S1,W4=>false
|StD,S0,W4=>false
|StD,S1,W4=>false
|StA,S0,W5=>true
|StA,S1,W5=>true
|StB,S0,W5=>true
|StC,S0,W5=>true
|StC,S1,W5=>true
|StD,S0,W5=>true
|StD,S1,W5=>true
|StB,S1,_=>true end.
(* END GENERATED FINITE CERTIFICATE *)
Definition mw_inv(c:cconf):Prop:=let '(q,(L,h,R)):=c in mw_ok q h(mw_fold R)=true.
Lemma mw_empty:forall q L h,mw_inv(q,(L,h,[]))->(q,h)=(StB,S1).
Proof. intros q L h H;destruct q,h;cbn[mw_inv mw_fold mw_ok]in H;try discriminate;reflexivity. Qed.
Definition mw_guard:list Sym:=[S0;S0;S0;S1;S1;S0;S1;S1;S1;S1].
Lemma mw_seed:forall L,mw_inv(cL StD L mw_guard).
Proof. intro L;unfold mw_inv,cL;destruct(chd L);reflexivity. Qed.
Lemma mw_local:forall q h a r s,q<>StB \/ h<>S1 ->
 let tr:=match bm_tm q h with Some t=>t|None=>mkTrans S0 DR StA end in
 match t_dir tr with
 |DL=>implb(mw_ok q h s)(mw_ok(t_next tr)a(mw_cons(t_write tr)s))
 |DR=>implb(mw_ok q h(mw_cons r s))(mw_ok(t_next tr)r s)end=true.
Proof. intros q h a r s H;destruct q,h,a,r,s;cbn;intuition congruence. Qed.
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma mw_step:forall c d,cstep tm c=Some d->mw_inv c->cinstr c<>(StB,S1)->mw_inv d.
Proof.
 intros[q[[L h]R]] d HE HI HN.
 assert(HQ:q<>StB \/ h<>S1)by(destruct q,h;cbn[cinstr]in HN;intuition congruence).
 pose proof(mw_local q h(chd L)(chd R)(mw_fold R)HQ)as HP.
 pose proof(mw_local q h(chd L)(chd R)(mw_fold(ctl R))HQ)as HO.
 destruct R as[|r R].
 - pose proof(mw_empty q L h HI)as E;exfalso;apply HN;exact E.
 - unfold mw_inv in HI. unfold cstep in HE;rewrite Htm in HE.
   destruct q,h;cbn[bm_tm ctape_move t_dir t_write t_next]in HE;
   cbn[bm_tm t_dir t_write t_next]in HP,HO;
   injection HE as <-;unfold mw_inv;cbn[chd ctl mw_fold];
   cbn[mw_fold chd ctl]in HI,HP,HO;
   (rewrite HI in HP;exact HP)||(rewrite HI in HO;exact HO).
Qed.
End Machine.
Definition mw_P0:list Sym:=[S0;S1;S0;S0;S1].
Definition mw_P1:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1].
Section Macros.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Local Ltac run:=repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl cL]).
Lemma mw_phase0:forall U,Reach0 tm(StB,(mw_P0++U,S0,[]))(StB,(mw_P1++U,S0,[])).
Proof. intro U;eapply(r0_run _ 19);[unfold mw_P0,mw_P1;cbn[app];run;reflexivity|apply reach0_refl]. Qed.
Lemma mw_phase1:forall U,Reach0 tm(StB,(mw_P1++U,S0,[]))(cL StD U mw_guard).
Proof. intro U;eapply(r0_run _ 29);[unfold mw_P1,mw_guard;cbn[app];run;reflexivity|apply reach0_refl]. Qed.
End Macros.
