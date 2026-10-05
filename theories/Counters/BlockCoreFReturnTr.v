(** * Counters.BlockCoreFReturnTr: protected suffixes for block-list core F

    Canonical table: [0LB0LC_1RD1LA_1RB1LB_1LA0RD].  A marked C1
    configuration has a left word consisting solely of ones, or ending
    in 1111.  The right word starts in 01 and continues with tokens 1/01.

    The protected D family has left word 0^n 011 W, where W is 11, 111,
    or ends in 1111.  D consumes right ones by extending 0^n.  On a zero,
    n=0 scans the leading zeros of W until reaching a 1; n=1 returns
    immediately; n>=2 consumes the zero and rebuilds the protected prefix.
    Induction on the finite right word closes this family, with explicit
    blank-boundary cases.  A consumes left pairs 01 until it returns to
    C1 or enters that D family.  Four short pure-one left words handle
    the finite left boundary; every longer one returns in three steps.

    [bf_return] gives a positive marked return.  Its only axiom is
    functional_extensionality_dep, inherited from tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bf_guard:list Sym:=[S1;S1;S1;S1].
Inductive bf_left:list Sym->Prop:=
| bf_pure:forall n,bf_left(rep[S1]n)
| bf_long:forall U,bf_left(U++bf_guard).
Inductive bf_tail:list Sym->Prop:=
| bf_two:bf_tail[S1;S1]
| bf_three:bf_tail[S1;S1;S1]
| bf_four:forall U,bf_tail(U++bf_guard).
Inductive bf_right:list Sym->Prop:=
| bf_nil:bf_right[]
| bf_one:forall R,bf_right R->bf_right(S1::R)
| bf_pair:forall R,bf_right R->bf_right(S0::S1::R).
Lemma bf_right_tail:forall x R,bf_right(x::R)->bf_right R.
Proof. intros x R H;inversion H;subst;[assumption|apply bf_one;assumption]. Qed.
Lemma bf_left_one:forall W,bf_left W->bf_left(S1::W).
Proof. intros W H;inversion H;subst;[change(bf_left(rep[S1](S n)));apply bf_pure|change(bf_left((S1::U)++bf_guard));apply bf_long]. Qed.
Lemma bf_tail_left:forall W,bf_tail W->bf_left W.
Proof. intros W H;inversion H;subst;[exact(bf_pure 2)|exact(bf_pure 3)|apply bf_long]. Qed.
Lemma bf_tail_nonempty:forall W,bf_tail W->W<>[].
Proof. intros W H;inversion H;subst;try discriminate. destruct U;discriminate. Qed.
Lemma bf_tail_zero:forall W,bf_tail(S0::W)->bf_tail W.
Proof.
 intros W H;inversion H;subst. destruct U as[|x U];[discriminate|].
 match goal with E : _ = _ |- _ => inversion E;subst end. apply bf_four.
Qed.
Lemma bf_tail_one:forall W,bf_tail(S1::W)->bf_left W.
Proof.
 intros W H;inversion H;subst;[exact(bf_pure 1)|exact(bf_pure 2)|].
 destruct U as[|x U].
 - match goal with E : _ = _ |- _ => cbn[app bf_guard]in E;inversion E;subst end;exact(bf_pure 3).
 - match goal with E : _ = _ |- _ => inversion E;subst end;apply bf_long.
Qed.
Lemma bf_tail_boost:forall n W,bf_tail W->bf_tail(rep[S0]n++S1::S1::W).
Proof.
 intros n W H;inversion H;subst.
 - apply bf_four.
 - replace(rep[S0]n++[S1;S1;S1;S1;S1])with((rep[S0]n++[S1])++bf_guard)by now rewrite <-app_assoc. apply bf_four.
 - replace(rep[S0]n++S1::S1::(U++bf_guard))with((rep[S0]n++S1::S1::U)++bf_guard)by now rewrite <-app_assoc.
   apply bf_four.
Qed.
Inductive bf_mark:cconf->Prop:=
| bf_anchor:forall L R,bf_left L->bf_right R->bf_mark(StC,(L,S1,S0::S1::R)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DL StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StD))
 (HB1:tm StB S1=Some(mkTrans S1 DL StA))
 (HC0:tm StC S0=Some(mkTrans S1 DR StB))
 (HC1:tm StC S1=Some(mkTrans S1 DL StB))
 (HD0:tm StD S0=Some(mkTrans S1 DL StA))
 (HD1:tm StD S1=Some(mkTrans S0 DR StD)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bf_guard];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bf_guard]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Definition bf_hit(c:cconf):Prop:=exists d,bf_mark d/\Reach0 tm c d.
Lemma bf_back:forall c d,Reach0 tm c d->bf_hit d->bf_hit c.
Proof. intros c d H(e&He&Hr);exists e;split;[exact He|eapply reach0_trans;eauto]. Qed.
Lemma bf_here:forall c,bf_mark c->bf_hit c.
Proof. intros;exists c;split;[assumption|r0]. Qed.
(** This branch scans a finite prefix of zeros in the protected tail,
    manufacturing a right 1 each time; the tail guard prevents a blank loop. *)
Lemma bf_D_zero:forall W R,bf_tail W->bf_right R->
 bf_hit(cR StD(S0::S1::S1::W)(S0::R)).
Proof.
 fix IH 1. intros W R HW HR. destruct W as[|[]W].
 - exfalso;apply(bf_tail_nonempty _ HW);reflexivity.
 - eapply bf_back;[go 7;r0|]. apply IH;[apply bf_tail_zero;exact HW|apply bf_one;exact HR].
 - eapply bf_back;[go 4;r0|]. apply bf_here,bf_anchor.
   + apply bf_tail_one;exact HW.
   + apply bf_pair;exact HR.
Qed.
Lemma bf_D_onezero:forall W R,bf_tail W->bf_right R->
 bf_hit(cR StD(S0::S0::S1::S1::W)(S0::R)).
Proof.
 intros. eapply bf_back;[go 5;r0|]. apply bf_here,bf_anchor.
 - apply bf_left_one,bf_tail_left;assumption.
 - apply bf_one;assumption.
Qed.
Lemma bf_D_manyzero:forall n W R,
 Reach0 tm(cR StD(rep[S0](S(S n))++S0::S1::S1::W)(S0::R))
 (cR StD(S0::S0::S1::S1::(rep[S0]n++S1::S1::W))R).
Proof. intros. cbn[rep app]. rewrite rep1_snoc. go 9;r0. Qed.
(** Every recursive call consumes a right cell.  The empty right word
    is handled separately using its implicit blank. *)
Lemma bf_D_return:forall R n W,bf_right R->bf_tail W->
 bf_hit(cR StD(rep[S0]n++S0::S1::S1::W)R).
Proof.
 fix IH 1. intros R n W HR HW. destruct R as[|[]R].
 - destruct n as[|[|n]].
   + apply bf_D_zero;[exact HW|apply bf_nil].
   + apply bf_D_onezero;[exact HW|apply bf_nil].
   + eapply bf_back;[apply(bf_D_manyzero n W [])|].
     apply bf_D_onezero;[apply bf_tail_boost;exact HW|apply bf_nil].
 - pose proof(bf_right_tail _ _ HR)as HT. destruct n as[|[|n]].
   + apply bf_D_zero;[exact HW|exact HT].
   + apply bf_D_onezero;[exact HW|exact HT].
   + eapply bf_back;[apply bf_D_manyzero|].
     change(bf_hit(cR StD(rep[S0]1++S0::S1::S1::(rep[S0]n++S1::S1::W))R)).
     apply IH;[exact HT|apply bf_tail_boost;exact HW].
 - pose proof(bf_right_tail _ _ HR)as HT. eapply bf_back;[go 1;r0|].
   change(bf_hit(cR StD(rep[S0](S n)++S0::S1::S1::W)R)).
   apply IH;assumption.
Qed.
Lemma bf_C_guard:forall U R,bf_right R->
 bf_hit(cL StC(U++bf_guard)(S0::S1::R)).
Proof.
 intros U R HR. destruct U as[|[]U].
 - apply bf_here,bf_anchor;[exact(bf_pure 3)|exact HR].
 - eapply bf_back;[go 3;r0|].
   change(bf_hit(cR StD(rep[S0]0++S0::S1::S1::(U++bf_guard))R)).
   apply bf_D_return;[exact HR|apply bf_four].
 - apply bf_here,bf_anchor;[apply bf_long|exact HR].
Qed.
Lemma bf_A_guard:forall U R,bf_right R->
 bf_hit(cL StA(U++bf_guard)(S1::R)).
Proof.
 fix IH 1. intros U R HR. destruct U as[|[]U].
 - eapply bf_back;[go 1;r0|]. apply bf_here,bf_anchor;[exact(bf_pure 2)|exact HR].
 - destruct U as[|[]U].
   + eapply bf_back;[go 3;r0|]. apply bf_here,bf_anchor;[exact(bf_pure 1)|apply bf_pair;exact HR].
   + eapply bf_back;[go 4;r0|]. apply bf_C_guard,bf_one;exact HR.
   + eapply bf_back;[go 2;r0|]. apply IH,bf_pair;exact HR.
 - eapply bf_back;[go 1;r0|]. apply bf_C_guard;exact HR.
Qed.
Definition bf_pos(c:cconf):Prop:=exists d,bf_mark d/\Reach1 tm c d.
Lemma bf_start:forall n c d,0<n->csteps tm n c=Some d->bf_hit d->bf_pos c.
Proof. intros n c d Hn Hrun(e&He&Hr);exists e;split;[exact He|eapply r1_run;eauto]. Qed.
Lemma bf_return_empty:forall R,bf_right R->bf_pos(StC,([],S1,S0::S1::R)).
Proof.
 intros. eapply(bf_start 19);[lia|run|]. apply bf_here,bf_anchor.
 - exact(bf_pure 1).
 - apply bf_one,bf_one,bf_one;assumption.
Qed.
Lemma bf_return_one:forall R,bf_right R->bf_pos(StC,([S1],S1,S0::S1::R)).
Proof.
 intros. eapply(bf_start 21);[lia|run|].
 change(bf_hit(cR StD(rep[S0]2++S0::S1::S1::[S1;S1])R)).
 apply bf_D_return;[assumption|apply bf_two].
Qed.
Lemma bf_return_two:forall R,bf_right R->bf_pos(StC,([S1;S1],S1,S0::S1::R)).
Proof.
 intros. eapply(bf_start 12);[lia|run|]. apply bf_here,bf_anchor.
 - exact(bf_pure 1).
 - apply bf_one,bf_one;assumption.
Qed.
Lemma bf_return_three:forall L R,bf_left L->bf_right R->
 bf_pos(StC,(S1::S1::S1::L,S1,S0::S1::R)).
Proof.
 intros. eapply(bf_start 3);[lia|run|]. apply bf_here,bf_anchor.
 - assumption.
 - apply bf_one,bf_pair;assumption.
Qed.
Lemma bf_return_long:forall U R,bf_right R->
 bf_pos(StC,(U++bf_guard,S1,S0::S1::R)).
Proof.
 intros U R HR. destruct U as[|[]U].
 - apply bf_return_three;[exact(bf_pure 1)|exact HR].
 - eapply(bf_start 6);[lia|run|]. apply bf_A_guard,bf_pair,bf_one;exact HR.
 - eapply(bf_start 2);[lia|run|]. apply bf_A_guard,bf_one,bf_pair;exact HR.
Qed.
Theorem bf_return:forall c,bf_mark c->exists d,bf_mark d/\Reach1 tm c d.
Proof.
 intros c H;change(bf_pos c);inversion H;subst. inversion H0;subst.
 - destruct n as[|[|[|n]]].
   + apply bf_return_empty;assumption.
   + apply bf_return_one;assumption.
   + apply bf_return_two;assumption.
   + apply bf_return_three;[apply bf_pure|assumption].
 - apply bf_return_long;assumption.
Qed.
End Machine.
Lemma bf_mark_instr:forall c,bf_mark c->cinstr c=(StC,S1).
Proof. intros c H;inversion H;reflexivity. Qed.

