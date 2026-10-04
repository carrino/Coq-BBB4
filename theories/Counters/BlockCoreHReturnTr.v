(** * Counters.BlockCoreHReturnTr: alternating terminal guards for core H

    Canonical table: [0LB1RC_1LC0RB_1RD0LC_0RB0RA].  The marked A1
    family has left word 01 L, where L starts from 1 and is extended by
    prefixes 1/01.  Its right word is 0 W: W is empty, is 10, or starts
    from 1010 and is extended by prefixes 0/10.  The last zero is an
    explicit blank, so the normalized right word is empty, 01, or has
    a terminal 0101 guard.

    A protected C pass has right word 0^n 010 W with nonempty W.  It
    consumes left ones by increasing n.  On a left zero, n=0 enters an
    A scan of leading right zeros, n=1 returns to A1, and n>=2 rebuilds
    the protected right word.  The finite left grammar supports this
    induction, including the implicit blank after its last 1.

    [bh_return] starts every branch with a positive concrete run and
    returns to the marked family.  The only axiom is
    functional_extensionality_dep, inherited from tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Inductive bh_left:list Sym->Prop:=
| bh_last:bh_left[S1]
| bh_lone:forall L,bh_left L->bh_left(S1::L)
| bh_lpair:forall L,bh_left L->bh_left(S0::S1::L).
Inductive bh_long:list Sym->Prop:=
| bh_base:bh_long[S1;S0;S1;S0]
| bh_zero:forall W,bh_long W->bh_long(S0::W)
| bh_ten:forall W,bh_long W->bh_long(S1::S0::W).
Inductive bh_tail:list Sym->Prop:=
| bh_short:bh_tail[S1;S0]
| bh_full:forall W,bh_long W->bh_tail W.
Inductive bh_rest:list Sym->Prop:=
| bh_empty:bh_rest[]
| bh_nonempty:forall W,bh_tail W->bh_rest W.
Lemma bh_tail_notnil:forall W,bh_tail W->W<>[].
Proof. intros W H;inversion H;subst;[discriminate|inversion H0;discriminate]. Qed.
Lemma bh_tail_zero:forall W,bh_tail(S0::W)->bh_long W.
Proof. intros W H;inversion H;subst;inversion H0;subst;assumption. Qed.
Lemma bh_tail_one:forall W,bh_tail(S1::W)->exists V,W=S0::V/\bh_rest V.
Proof.
 intros W H;inversion H;subst.
 - exists[];split;[reflexivity|apply bh_empty].
 - inversion H0;subst.
   + exists[S1;S0];split;[reflexivity|apply bh_nonempty,bh_short].
   + exists W0;split;[reflexivity|apply bh_nonempty,bh_full;assumption].
Qed.
Lemma bh_tail_boost:forall n W,bh_tail W->bh_tail(rep[S0]n++S1::S0::W).
Proof.
 intros n W H;apply bh_full. induction n;cbn[rep app];[|apply bh_zero;exact IHn].
 inversion H;subst;[apply bh_base|apply bh_ten;assumption].
Qed.
Inductive bh_mark:cconf->Prop:=
| bh_anchor:forall L W,bh_left L->bh_rest W->bh_mark(StA,(S0::S1::L,S1,S0::W)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DL StB))
 (HA1:tm StA S1=Some(mkTrans S1 DR StC))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StB))
 (HC0:tm StC S0=Some(mkTrans S1 DR StD))
 (HC1:tm StC S1=Some(mkTrans S0 DL StC))
 (HD0:tm StD S0=Some(mkTrans S0 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Definition bh_hit(c:cconf):Prop:=exists d,bh_mark d/\Reach0 tm c d.
Lemma bh_back:forall c d,Reach0 tm c d->bh_hit d->bh_hit c.
Proof. intros c d H(e&He&Hr);exists e;split;[exact He|eapply reach0_trans;eauto]. Qed.
Lemma bh_here:forall c,bh_mark c->bh_hit c.
Proof. intros;exists c;split;[assumption|r0]. Qed.
Lemma bh_A_scan:forall W L,bh_tail W->bh_left L->
 bh_hit(cR StA(S0::S1::S0::S1::L)W).
Proof.
 fix IH 1. intros W L HW HL. destruct W as[|[]W].
 - exfalso;apply(bh_tail_notnil _ HW);reflexivity.
 - eapply bh_back;[go 9;r0|]. apply IH;[apply bh_full,bh_tail_zero;exact HW|apply bh_lone;exact HL].
 - destruct(bh_tail_one _ HW)as(V&E&HV);subst.
   apply bh_here,bh_anchor;[apply bh_lpair;exact HL|exact HV].
Qed.
Lemma bh_C_zero:forall L W,bh_tail W->bh_left L->
 bh_hit(cL StC(S0::L)(S0::S1::S0::W)).
Proof.
 intros. eapply bh_back;[go 6;r0|]. apply bh_A_scan;assumption.
Qed.
Lemma bh_C_onezero:forall L W,bh_tail W->bh_left L->
 bh_hit(cL StC(S0::L)(S0::S0::S1::S0::W)).
Proof.
 intros. eapply bh_back;[go 5;r0|]. apply bh_here,bh_anchor;[apply bh_lone;assumption|apply bh_nonempty;assumption].
Qed.
Lemma bh_C_manyzero:forall n L W,
 Reach0 tm(cL StC(S0::L)(rep[S0](S(S n))++S0::S1::S0::W))
 (cL StC L(S0::S0::S1::S0::(rep[S0]n++S1::S0::W))).
Proof. intros. cbn[rep app]. rewrite rep1_snoc. go 9;r0. Qed.
Lemma bh_C_blank:forall n W,bh_tail W->
 bh_hit(cL StC[](rep[S0](S n)++S0::S1::S0::W)).
Proof.
 intros[|n]W HW.
 - eapply bh_back;[go 5;r0|]. apply bh_here,bh_anchor;[apply bh_last|apply bh_nonempty;exact HW].
 - eapply bh_back;[apply(bh_C_manyzero n [] W)|].
   eapply bh_back;[go 5;r0|]. apply bh_here,bh_anchor;[apply bh_last|apply bh_nonempty,bh_tail_boost;exact HW].
Qed.
(** The grammar derivation is finite.  A 1 prefix is consumed directly;
    after a continuing 01 branch, its 1 is consumed before the recursive
    call.  The final singleton 1 reaches the explicit blank case. *)
Lemma bh_C_return:forall L,bh_left L->forall n W,bh_tail W->
 bh_hit(cL StC L(rep[S0]n++S0::S1::S0::W)).
Proof.
 intros L HL;induction HL;intros n W HW.
 - eapply bh_back;[go 1;r0|].
   change(bh_hit(cL StC[](rep[S0](S n)++S0::S1::S0::W))). apply bh_C_blank;exact HW.
 - eapply bh_back;[go 1;r0|].
   change(bh_hit(cL StC L(rep[S0](S n)++S0::S1::S0::W))). apply IHHL;exact HW.
 - destruct n as[|[|n]].
   + apply bh_C_zero;[exact HW|apply bh_lone;exact HL].
   + apply bh_C_onezero;[exact HW|apply bh_lone;exact HL].
   + eapply bh_back;[apply bh_C_manyzero|]. eapply bh_back;[go 1;r0|].
     change(bh_hit(cL StC L(rep[S0]2++S0::S1::S0::(rep[S0]n++S1::S0::W)))).
     apply IHHL,bh_tail_boost;exact HW.
Qed.
Lemma bh_A_frontier:forall L W,bh_left L->bh_tail W->
 bh_hit(cR StA(S0::S1::L)W).
Proof.
 intros L W HL HW. destruct W as[|[]W].
 - exfalso;apply(bh_tail_notnil _ HW);reflexivity.
 - eapply bh_back;[go 3;r0|].
   change(bh_hit(cL StC L(rep[S0]0++S0::S1::S0::W))).
   apply bh_C_return;[exact HL|apply bh_full,bh_tail_zero;exact HW].
 - destruct(bh_tail_one _ HW)as(V&E&HV);subst. apply bh_here,bh_anchor;assumption.
Qed.
Lemma bh_B_frontier:forall L W,bh_left L->bh_long W->
 bh_hit(cR StB(S0::S1::S1::L)W).
Proof.
 intros L W HL HW. inversion HW;subst.
 - eapply bh_back;[go 4;r0|]. change(bh_hit(cR StA(S0::S1::S0::S1::S1::L)[S1;S0])). apply bh_A_frontier;[apply bh_lpair,bh_lone;exact HL|apply bh_short].
 - eapply bh_back;[go 3;r0|]. apply bh_A_frontier;[apply bh_lone,bh_lone;exact HL|apply bh_full;assumption].
 - eapply bh_back;[go 4;r0|]. apply bh_A_frontier;[apply bh_lpair,bh_lone;exact HL|apply bh_full;assumption].
Qed.
Definition bh_pos(c:cconf):Prop:=exists d,bh_mark d/\Reach1 tm c d.
Lemma bh_start:forall n c d,0<n->csteps tm n c=Some d->bh_hit d->bh_pos c.
Proof. intros n c d Hn Hrun(e&He&Hr);exists e;split;[exact He|eapply r1_run;eauto]. Qed.
Theorem bh_return:forall c,bh_mark c->exists d,bh_mark d/\Reach1 tm c d.
Proof.
 intros c H;change(bh_pos c);inversion H;subst. inversion H1;subst.
 - eapply(bh_start 21);[lia|run|].
   change(bh_hit(cL StC L(rep[S0]2++S0::S1::S0::[S1;S0]))).
   apply bh_C_return;[assumption|apply bh_short].
 - destruct W as[|[]W].
   + exfalso;apply(bh_tail_notnil _ H2);reflexivity.
   + eapply(bh_start 3);[lia|run|]. apply bh_B_frontier.
     * apply bh_lpair;assumption.
     * apply bh_tail_zero;assumption.
   + destruct(bh_tail_one _ H2)as(V&E&HV);subst.
     eapply(bh_start 12);[lia|run|]. apply bh_here,bh_anchor.
     * apply bh_lone,bh_lone;assumption.
     * exact HV.
Qed.
End Machine.
Lemma bh_mark_instr:forall c,bh_mark c->cinstr c=(StA,S1).
Proof. intros c H;inversion H;reflexivity. Qed.
