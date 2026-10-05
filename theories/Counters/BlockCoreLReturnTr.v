(** Exact finite-word carries of the block-list L machine. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Inductive bl_word_map:list Sym->list Sym->Prop:=
| blw_base:bl_word_map[S1][S1;S1;S0;S1]
| blw_stop:forall x,bl_word_map(S1::S0::S1::x)(S1::S1::S1::S1::x)
| blw_carry11:forall x v,bl_word_map(S1::x)v->
 bl_word_map(S1::S1::S1::x)(S1::S0::v)
| blw_carry110:forall x v,bl_word_map(S1::x)v->
 bl_word_map(S1::S1::S0::S1::x)(S1::S0::S1::v).
Definition bl_anchor(w:list Sym):cconf:=(StB,(w,S0,[])).
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S1 DR StA))
 (HB0:tm StB S0=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StA))
 (HC0:tm StC S0=Some(mkTrans S1 DL StC))
 (HC1:tm StC S1=Some(mkTrans S1 DL StD))
 (HD0:tm StD S0=Some(mkTrans S1 DL StA))
 (HD1:tm StD S1=Some(mkTrans S0 DL StC)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bl_anchor];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bl_anchor]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Theorem bl_C_map:forall w v,bl_word_map w v->exists t,v=S1::t/\
 forall R,Reach0 tm(cL StC w R)(cR StA t R).
Proof.
 intros w v H;induction H.
 - exists[S1;S0;S1];split;[reflexivity|]. intros;go 5;r0.
 - exists(S1::S1::S1::x);split;[reflexivity|]. intros;go 5;r0.
 - destruct IHbl_word_map as(t&->&HT).
   exists(S0::S1::t);split;[reflexivity|]. intros R;go 2.
   rt(HT(S0::S1::R));go 2;r0.
 - destruct IHbl_word_map as(t&->&HT).
   exists(S0::S1::S1::t);split;[reflexivity|]. intros R;go 3.
   rt(HT(S1::S0::S1::R));go 3;r0.
Qed.
Theorem bl_lap:forall w v,bl_word_map w v->Reach1 tm(bl_anchor w)(bl_anchor v).
Proof.
 intros w v H;destruct(bl_C_map w v H)as(t&->&HT).
 go 1;rt(HT[S0]);go 1;r0.
Qed.
Lemma bl_C_D0:forall w v,bl_word_map w v->forall R,Fires tm(cL StC w R)(StD,S0).
Proof.
 intros w v H;induction H;intro R.
 - exists 1;eexists;split;[run|reflexivity].
 - exists 1;eexists;split;[run|reflexivity].
 - eapply fire_back;[go 2;r0|apply IHbl_word_map].
 - eapply fire_back;[go 3;r0|apply IHbl_word_map].
Qed.
Lemma bl_C_A1:forall w v,bl_word_map w v->forall R,Fires tm(cL StC w R)(StA,S1).
Proof.
 intros w v H;induction H;intro R.
 - exists 4;eexists;split;[run|reflexivity].
 - exists 2;eexists;split;[run|reflexivity].
 - eapply fire_back;[go 2;r0|apply IHbl_word_map].
 - eapply fire_back;[go 3;r0|apply IHbl_word_map].
Qed.
Lemma bl_C_carry_B1:forall x v,bl_word_map(S1::x)v->forall R,
 Fires tm(cL StC(S1::S1::S1::x)R)(StB,S1).
Proof.
 intros x v H R;destruct(bl_C_map _ _ H)as(t&->&HT).
 eapply fire_back;[go 2;r0|].
 eapply fire_back;[apply(HT(S0::S1::R))|].
 exists 1;eexists;split;[run|reflexivity].
Qed.
Theorem bl_anchor_fires:forall x v,bl_word_map(S1::S1::S1::S1::S0::x)v->
 forall q,Fires tm(bl_anchor(S1::S1::S1::S1::S0::x))q.
Proof.
 intros x v H[q h];destruct q,h.
 - destruct(bl_C_map _ _ H)as(t&->&HT).
   eapply fire_back;[go 1;r0|]. eapply fire_back;[apply(HT[S0])|].
   apply fires_here;reflexivity.
 - eapply fire_back;[go 1;r0|]. exact(bl_C_A1 _ _ H[S0]).
 - apply fires_here;reflexivity.
 - inversion H;subst.
   eapply fire_back;[go 1;r0|]. apply(bl_C_carry_B1(S1::S0::x) _ H1 [S0]).
 - exists 5;eexists;split;[run|reflexivity].
 - exists 1;eexists;split;[run|reflexivity].
 - eapply fire_back;[go 1;r0|]. exact(bl_C_D0 _ _ H[S0]).
 - exists 2;eexists;split;[run|reflexivity].
Qed.
End Core.
