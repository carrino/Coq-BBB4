(** The three finite boundary words of the paired-zero return wall. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Counters Require Import BlockCoreELeftTr.
Import ListNotations.
Definition bew_P:list Sym:=[S1;S1;S0;S0;S1;S1;S1].
Definition bew_Q:list Sym:=[S0;S0;S1;S0;S1;S1;S1].
Definition bew_J:list Sym:=[S1;S0;S1;S0;S1;S1;S1].
Definition bew_exit:list Sym:=[S1;S1;S0;S1;S0;S1].
Definition bew_word(W:list Sym):Prop:=W=bew_P\/W=bew_Q\/W=bew_J.
Section Core.
Variable tm:TM.
Hypotheses
 (HA1:tm StA S1=Some(mkTrans S1 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StA))
 (HB1:tm StB S1=Some(mkTrans S0 DL StC))
 (HC0:tm StC S0=Some(mkTrans S0 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StC))
 (HD1:tm StD S1=Some(mkTrans S1 DR StD)).
Definition bew_hit(R:list Sym)(c:cconf):Prop:=
 exists W,bew_word W/\bel_hit tm(W++R)c.
Definition bew_result(R:list Sym)(c:cconf):Prop:=
 bew_hit R c\/exists V,Reach0 tm c(cR StD(bew_exit++V)R).
Lemma bew_back:forall R c d,Reach0 tm c d->bew_result R d->bew_result R c.
Proof.
 intros R c d H[HH|(V&HR)].
 - left;destruct HH as(W&HW&HH);exists W;split;[exact HW|eapply bel_hit_back;eauto].
 - right;exists V;eapply reach0_trans;eauto.
Qed.
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bew_P bew_Q bew_J bew_exit];
 repeat(first[rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bew_P bew_Q bew_J bew_exit]);reflexivity.
Local Ltac go n:=eapply(r0_run _ n);[run|].
Lemma bew_CP:forall L R,Reach0 tm(cR StC L(bew_P++R))(cL StA L(bew_Q++R)).
Proof. intros;go 7;r0. Qed.
Lemma bew_DP:forall L R,Reach0 tm(cR StD L(bew_P++R))(cR StD(bew_exit++S0::L)R).
Proof. intros;go 13;r0. Qed.
Lemma bew_CQ:forall L R,Reach0 tm(cR StC L(bew_Q++R))(cL StA L(bew_Q++R)).
Proof. intros;go 1;r0. Qed.
Lemma bew_DQ:forall L R,Reach0 tm(cR StD L(bew_Q++R))(cL StB L(bew_J++R)).
Proof. intros;go 3;r0. Qed.
Lemma bew_CJ:forall L R,Reach0 tm(cR StC L(bew_J++R))(cR StD(bew_exit++S0::L)R).
Proof. intros;go 7;r0. Qed.
Lemma bew_DJ:forall L R,Reach0 tm(cR StD L(bew_J++R))(cR StD(bew_exit++S1::L)R).
Proof. intros;go 7;r0. Qed.
Lemma bew_finite_bound:forall n L,bel_value L=n->forall W R q,
 bew_word W->bel_right q->bew_result R(cR q L(W++R)).
Proof.
 intro n;induction n using lt_wf_ind;intros L HV W R q HW HQ.
 assert(HL:forall W q,bew_word W->bel_left q->bew_result R(cL q L(W++R))).
 {
  intros V qq HW' HQ'.
  destruct(bel_excursion tm HA1 HB0 HB1 HC0 HC1 HD0 HD1 L(V++R)qq HQ')
    as[HH|(q'&L'&HQ''&HV'&HR)].
  - left;exists V;split;assumption.
  - eapply bew_back;[exact HR|].
    apply(H(bel_value L'));[lia|reflexivity|exact HW'|exact HQ''].
 }
 destruct HW as[-> | [-> | ->]];destruct HQ as[-> | ->].
 - eapply bew_back;[apply bew_CP|]. apply HL;[right;left;reflexivity|left;reflexivity].
 - right;exists(S0::L);apply bew_DP.
 - eapply bew_back;[apply bew_CQ|]. apply HL;[right;left;reflexivity|left;reflexivity].
 - eapply bew_back;[apply bew_DQ|]. apply HL;[right;right;reflexivity|right;left;reflexivity].
 - right;exists(S0::L);apply bew_CJ.
 - right;exists(S1::L);apply bew_DJ.
Qed.
Theorem bew_finite:forall L W R q,bew_word W->bel_right q->
 bew_result R(cR q L(W++R)).
Proof. intros;apply(bew_finite_bound(bel_value L));auto. Qed.
Theorem bew_left_finite:forall L W R q,bew_word W->bel_left q->
 bew_result R(cL q L(W++R)).
Proof.
 intros L W R q HW HQ.
 destruct(bel_excursion tm HA1 HB0 HB1 HC0 HC1 HD0 HD1 L(W++R)q HQ)
 as[HH|(qq&V&HQ'&HV&HR)].
 - left;exists W;split;assumption.
 - eapply bew_back;[exact HR|]. apply bew_finite;assumption.
Qed.
(** Every finite prefix is consumed, retaining one of the three walls. *)
Theorem bew_right_prefix:forall W R,bew_word W->forall P L q,bel_right q->
 bew_result R(cR q L(P++W++R)).
Proof.
 intros W R HW P;induction P as[|d P IH];intros L q HQ.
 - change(bew_result R(cR q L(W++R))). exact(bew_finite L W R q HW HQ).
 - destruct HQ as[-> | ->];destruct d.
   + change(bew_result R(cL StC(S0::L)(P++W++R))).
     destruct(bel_excursion tm HA1 HB0 HB1 HC0 HC1 HD0 HD1(S0::L)(P++W++R)StC
       ltac:(right;right;reflexivity))as[HH|(qq&V&Hq&Hlt&HR)].
     * left;exists W;split;[exact HW|apply(bel_hit_prefix tm P);exact HH].
     * eapply bew_back;[exact HR|]. apply IH;exact Hq.
   + eapply bew_back;[go 1;r0|]. apply IH;right;reflexivity.
   + eapply bew_back;[go 1;r0|]. apply IH;left;reflexivity.
   + eapply bew_back;[go 1;r0|]. apply IH;right;reflexivity.
Qed.
Theorem bew_left_prefix:forall L P W R q,bew_word W->bel_left q->
 bew_result R(cL q L(P++W++R)).
Proof.
 intros L P W R q HW HQ.
 destruct(bel_excursion tm HA1 HB0 HB1 HC0 HC1 HD0 HD1 L(P++W++R)q HQ)
 as[HH|(qq&V&Hq&Hlt&HR)].
 - left;exists W;split;[exact HW|apply(bel_hit_prefix tm P);exact HH].
 - eapply bew_back;[exact HR|]. apply bew_right_prefix;assumption.
Qed.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StA).
Local Ltac run_all:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bew_P bew_Q bew_J bew_exit];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bew_P bew_Q bew_J bew_exit]);reflexivity.
Lemma bew_AQ:forall L R,
 Reach1 tm(StA,(L,S0,bew_Q++R))(cR StD(bew_exit++S0::S1::L)R).
Proof. intros;eapply(r1_run _ 12);[lia|run_all|r0]. Qed.
Lemma bew_A1:forall L R,
 Reach1 tm(StA,(L,S0,S1::R))(cL StC L(S0::S1::R)).
Proof. intros;eapply(r1_run _ 3);[lia|run_all|r0]. Qed.
(** The first move of an A0 prefix-wall mark is positive; the remainder
    is discharged by the left and right prefix theorems above. *)
Theorem bew_A0_prefix:forall L P W R,bew_word W->
 (exists L' P' W',bew_word W'/\
  Reach1 tm(StA,(L,S0,P++W++R))(StA,(L',S0,P'++W'++R))) \/
 (exists V,Reach1 tm(StA,(L,S0,P++W++R))(cR StD(bew_exit++V)R)).
Proof.
 intros L P W R HW.
 assert(Hfinish:forall c,Reach1 tm(StA,(L,S0,P++W++R))c->bew_result R c->
 (exists L' P' W',bew_word W'/\
  Reach1 tm(StA,(L,S0,P++W++R))(StA,(L',S0,P'++W'++R))) \/
 (exists V,Reach1 tm(StA,(L,S0,P++W++R))(cR StD(bew_exit++V)R))).
 {
  intros c HC[(W'&HW'&L'&P'&HR)|(V&HR)].
  - left;exists L',P',W';split;[exact HW'|eapply reach10;eauto].
  - right;exists V;eapply reach10;eauto.
 }
 destruct P as[|[]P].
 - cbn[app]in*. destruct HW as[-> | [-> | ->]].
   + eapply Hfinish;[apply bew_A1|].
     change(bew_result R(cL StC L([S0]++bew_P++R))).
     apply bew_left_prefix;[left;reflexivity|right;right;reflexivity].
   + right;exists(S0::S1::L);apply bew_AQ.
   + eapply Hfinish;[apply bew_A1|].
     change(bew_result R(cL StC L([S0]++bew_J++R))).
     apply bew_left_prefix;[right;right;reflexivity|right;right;reflexivity].
 - left;exists(S1::L),P,W;split;[exact HW|].
   eapply(r1_run _ 1);[lia|run_all|r0].
 - eapply Hfinish;[apply bew_A1|].
   change(bew_result R(cL StC L((S0::S1::P)++W++R))).
   apply bew_left_prefix;[exact HW|right;right;reflexivity].
Qed.
End Core.
