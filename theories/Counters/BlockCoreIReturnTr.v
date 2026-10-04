(** * Counters.BlockCoreIReturnTr: marked returns for block-list core I

    The transition table is [0LB0RC_1LC1LA_1RD0LA_1RA0RD].  Its C1
    instruction recurs from a finite-word invariant rather than from every
    finite configuration.  All words are written nearest cell first.

    Put B = 01 and let a marker T be either 001 or 101.  A good left word
    ends in an odd run of B tokens; earlier B runs may have arbitrary length
    and are separated by markers.  The right word has no adjacent ones.
    Marked C1 configurations either have a good left word and a right word
    beginning in 1, or have an additional 001 marker on the left.

    The main helper consumes a safe right word at D, retaining a protected
    left prefix 101 B^k T W.  The finite boundary cases use blank padding.
    The C1 return follows by stripping B tokens and a marker.  At the final
    odd run, the blank-left excursion rebuilds a protected D prefix.

    [bi_return] gives a positive return to the marked family.  Its only
    axiom is functional_extensionality_dep, inherited from tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bi_B := [S0;S1].
Definition bi_T(b:bool) := if b then [S0;S0;S1] else [S1;S0;S1].
Inductive bi_good:list Sym->Prop :=
| bi_end:forall n,bi_good(rep bi_B(2*n+1))
| bi_more:forall k b W,bi_good W->bi_good(rep bi_B k++bi_T b++W).
Fixpoint bi_safe(R:list Sym):Prop:=match R with
|[]=>True|S0::R=>bi_safe R
|S1::R=>match R with S1::_=>False|_=>bi_safe R end end.
Lemma bi_safe_tail:forall x R,bi_safe(x::R)->bi_safe R.
Proof. intros[][|[]R];cbn;tauto. Qed.
Lemma bi_safe_zero:forall R,bi_safe R->bi_safe(S0::R).
Proof. auto. Qed.
Lemma bi_safe_pair:forall R,bi_safe R->bi_safe(S1::S0::R).
Proof. auto. Qed.
Lemma bi_safe_pairs:forall n R,bi_safe R->bi_safe(rep[S1;S0]n++R).
Proof. induction n;intros;cbn[rep app bi_safe];auto. Qed.
Lemma bi_good_BB:forall W,bi_good W->bi_good(bi_B++bi_B++W).
Proof.
 intros W H;inversion H;subst.
 - replace(bi_B++bi_B++rep bi_B(2*n+1))with(rep bi_B(2*S n+1))by(replace(2*S n+1)with(S(S(2*n+1)))by lia;reflexivity).
   apply bi_end.
 - change(bi_good(rep bi_B(S(S k))++bi_T b++W0)). apply bi_more;assumption.
Qed.
Inductive bi_mark:cconf->Prop:=
| bi_core:forall W R,bi_good W->bi_safe(S1::R)->bi_mark(StC,(W,S1,S1::R))
| bi_phase:forall W R,bi_good W->bi_safe R->bi_mark(StC,(bi_T true++W,S1,R)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DL StB))
 (HA1:tm StA S1=Some(mkTrans S0 DR StC))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DL StA))
 (HC0:tm StC S0=Some(mkTrans S1 DR StD))
 (HC1:tm StC S1=Some(mkTrans S0 DL StA))
 (HD0:tm StD S0=Some(mkTrans S1 DR StA))
 (HD1:tm StD S1=Some(mkTrans S0 DR StD)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bi_B bi_T];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bi_B bi_T]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Definition bi_hit(c:cconf):Prop:=exists d,bi_mark d /\ Reach0 tm c d.
Lemma bi_back:forall c d,Reach0 tm c d->bi_hit d->bi_hit c.
Proof. intros c d H(e&He&Hr);exists e;split;[exact He|eapply reach0_trans;eauto]. Qed.
Lemma bi_here:forall c,bi_mark c->bi_hit c.
Proof. intros;exists c;split;[assumption|r0]. Qed.
Lemma bi_A_pairs:forall n L R,
 Reach0 tm(cL StA(rep bi_B n++L)R)(cL StA L(rep[S1;S0]n++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma bi_A_marker:forall b W R,bi_good W->bi_safe(S1::R)->
 bi_hit(cL StA(bi_T b++W)(S1::R)).
Proof.
 intros[]W R HW HR.
 - eapply bi_back;[go 2;r0|]. apply bi_here,bi_core;[exact HW|apply bi_safe_pair;exact HR].
 - eapply bi_back;[go 1;r0|]. apply bi_here,bi_phase;[exact HW|eapply bi_safe_tail;exact HR].
Qed.
Lemma bi_D_zero:forall k b W R,bi_good W->bi_safe R->
 bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)(S0::S0::R)).
Proof.
 intros. eapply bi_back;[go 4;r0|]. apply bi_here,bi_phase.
 - apply bi_more;assumption.
 - exact H0.
Qed.
Lemma bi_D_100:forall k b W R,bi_good W->bi_safe R->
 bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)(S1::S0::S0::R)).
Proof.
 intros. eapply bi_back;[go 8;r0|].
 eapply bi_back;[apply bi_A_pairs|].
 destruct k;cbn[rep app].
 - apply bi_A_marker;[assumption|exact H0].
 - apply bi_A_marker;[assumption|apply bi_safe_pairs;exact H0].
Qed.
Lemma bi_D_010:forall L R,
 Reach0 tm(cR StD L(S0::S1::S0::R))(cR StD([S1;S0;S1]++L)R).
Proof. intros;go 3;r0. Qed.
Lemma bi_D_1010:forall L R,
 Reach0 tm(cR StD L(S1::S0::S1::S0::R))(cR StD([S1;S0;S1;S0]++L)R).
Proof. intros;go 4;r0. Qed.
Lemma bi_hit_lift:forall c d,lift c=lift d->bi_hit d->bi_hit c.
Proof. intros c d E(d'&H&Hreach);exists d';split;[exact H|eapply reach0_lift_l;eauto]. Qed.
Lemma bi_padR:forall q L h R,
 bi_hit(q,(L,h,R++[S0]))->bi_hit(q,(L,h,R)).
Proof.
 intros. eapply bi_hit_lift;[symmetry;apply(lift_padR 1)|exact H].
Qed.
Lemma bi_D_empty:forall k b W,bi_good W->
 bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[]).
Proof.
 intros. unfold cR;cbn[chd ctl]. apply bi_padR.
 change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S0;S0])).
 apply bi_D_zero;[assumption|exact I].
Qed.
(** The right sweep either stops at 00/100, or consumes 010/1010 while
    rebuilding the protected left prefix.  Induction is on the finite
    right word, including the explicit blank-boundary cases. *)
Lemma bi_D_protected:forall R k b W,bi_good W->bi_safe R->
 bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)R).
Proof.
 fix IH 1. intros R k b W HW HS. destruct R as[|[]R].
 - unfold cR;cbn[chd ctl]. apply bi_padR.
   change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S0;S0])).
   apply bi_D_zero;[exact HW|exact I].
 - destruct R as[|[]R].
   + unfold cR;cbn[chd ctl]. apply bi_padR.
     change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S0;S0])).
     apply bi_D_zero;[exact HW|exact I].
   + apply bi_D_zero;[exact HW|exact HS].
   + destruct R as[|[]R].
     * unfold cR;cbn[chd ctl]. apply bi_padR.
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S0;S1;S0])).
       eapply bi_back;[apply bi_D_010|].
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 0++bi_T false++(rep bi_B k++bi_T b++W))[])).
       apply bi_D_empty,bi_more;exact HW.
     * eapply bi_back;[apply bi_D_010|].
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 0++bi_T false++(rep bi_B k++bi_T b++W))R)).
       apply IH;[apply bi_more;exact HW|exact HS].
     * contradiction.
 - destruct R as[|[]R].
   + unfold cR;cbn[chd ctl]. apply bi_padR. apply bi_padR.
     change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S1;S0;S0])).
     apply bi_D_100;[exact HW|exact I].
   + destruct R as[|[]R].
     * unfold cR;cbn[chd ctl]. apply bi_padR.
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S1;S0;S0])).
       apply bi_D_100;[exact HW|exact I].
     * apply bi_D_100;[exact HW|exact HS].
     * destruct R as[|[]R].
       -- unfold cR;cbn[chd ctl]. apply bi_padR.
          change(bi_hit(cR StD([S1;S0;S1]++rep bi_B k++bi_T b++W)[S1;S0;S1;S0])).
          eapply bi_back;[apply bi_D_1010|].
          change(bi_hit(cR StD([S1;S0;S1]++rep bi_B(S(S k))++bi_T b++W)[])).
          apply bi_D_empty;exact HW.
       -- eapply bi_back;[apply bi_D_1010|].
          change(bi_hit(cR StD([S1;S0;S1]++rep bi_B(S(S k))++bi_T b++W)R)).
          apply IH;[exact HW|exact HS].
       -- contradiction.
   + contradiction.
Qed.
Definition bi_pos(c:cconf):Prop:=exists d,bi_mark d /\ Reach1 tm c d.
Lemma bi_start:forall n c d,0<n->csteps tm n c=Some d->bi_hit d->bi_pos c.
Proof. intros n c d Hn Hrun(e&He&Hr);exists e;split;[exact He|eapply r1_run;eauto]. Qed.
Lemma bi_phase_return:forall W R,bi_good W->bi_safe R->
 bi_pos(StC,(bi_T true++W,S1,R)).
Proof.
 intros. eapply(bi_start 3);[lia|run|]. apply bi_here,bi_core;[assumption|exact H0].
Qed.
Lemma bi_D_1001_stop:forall W R,bi_good W->bi_safe R->
 bi_hit(cR StD([S1;S0;S0;S1]++W)(S1::S0::S0::R)).
Proof.
 intros. eapply bi_back;[go 8;r0|]. apply bi_here,bi_core;[assumption|exact H0].
Qed.
Lemma bi_D_1001:forall W R,bi_good W->bi_safe(S1::R)->
 bi_hit(cR StD([S1;S0;S0;S1]++W)(S1::R)).
Proof.
 intros W R HW HS. destruct R as[|[]R].
 - unfold cR;cbn[chd ctl]. apply bi_padR,bi_padR.
   change(bi_hit(cR StD([S1;S0;S0;S1]++W)[S1;S0;S0])).
   apply bi_D_1001_stop;[exact HW|exact I].
 - destruct R as[|[]R].
   + unfold cR;cbn[chd ctl]. apply bi_padR.
     change(bi_hit(cR StD([S1;S0;S0;S1]++W)[S1;S0;S0])).
     apply bi_D_1001_stop;[exact HW|exact I].
   + apply bi_D_1001_stop;[exact HW|exact HS].
   + destruct R as[|[]R].
     * unfold cR;cbn[chd ctl]. apply bi_padR.
       change(bi_hit(cR StD([S1;S0;S0;S1]++W)[S1;S0;S1;S0])).
       eapply bi_back;[apply bi_D_1010|].
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 1++bi_T true++W)[])).
       apply bi_D_protected;[exact HW|exact I].
     * eapply bi_back;[apply bi_D_1010|].
       change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 1++bi_T true++W)R)).
       apply bi_D_protected;[exact HW|exact HS].
     * contradiction.
 - contradiction.
Qed.
Lemma bi_C_marker_return:forall b W R,bi_good W->bi_safe(S1::R)->
 bi_pos(StC,(bi_T b++W,S1,S1::R)).
Proof.
 intros[]W R HW HR.
 - apply bi_phase_return;assumption.
 - eapply(bi_start 3);[lia|run|]. apply bi_D_1001;assumption.
Qed.
Lemma bi_C_pairs_return:forall k b W R,bi_good W->bi_safe(S1::R)->
 bi_pos(StC,(rep bi_B(S k)++bi_T b++W,S1,S1::R)).
Proof.
 intros. eapply(bi_start 3);[lia|run|].
 eapply bi_back;[apply bi_A_pairs|]. destruct k;cbn[rep app].
 - apply bi_A_marker;[assumption|exact H0].
 - apply bi_A_marker;[assumption|apply bi_safe_pairs;exact H0].
Qed.
Lemma bi_D_blocks:forall n L R,
 Reach0 tm(cR StD L(rep[S1;S0;S1;S0]n++R))
          (cR StD(rep[S1;S0;S1;S0]n++L)R).
Proof. apply sweepR,bi_D_1010. Qed.
Lemma bi_A_blank:forall R,
 Reach0 tm(cL StA[](S1::S0::R))(cR StD[S1;S0;S1;S0;S1]R).
Proof. intros;go 7;r0. Qed.
Lemma bi_pairs_even:forall n R,
 rep[S1;S0](2*n)++S1::S0::S0::R =
 S1::S0::(rep[S1;S0;S1;S0]n++S0::R).
Proof.
 induction n;intros;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia. cbn[rep app]. now rewrite IHn.
Qed.
Lemma bi_blocks_left:forall n,
 rep[S1;S0;S1;S0]n++[S1;S0;S1;S0;S1]=
 [S1;S0;S1]++rep bi_B(2*n+1).
Proof.
 induction n;[reflexivity|].
 replace(2*S n+1)with(S(S(2*n+1)))by lia. cbn[rep app bi_B]. now rewrite IHn.
Qed.
(** Oddness of the last B run leaves an even number of 10 blocks after
    the blank-left turn.  These are exactly the blocks of the D sweep. *)
Lemma bi_terminal_return:forall n R,bi_safe(S1::R)->
 bi_pos(StC,(rep bi_B(2*n+1),S1,S1::R)).
Proof.
 intros n R HS. replace(2*n+1)with(S(2*n))by lia.
 eapply(bi_start 3);[lia|run|].
 change(bi_hit(cL StA(rep bi_B(2*n))(S1::S0::S0::S1::R))).
 rewrite <-(app_nil_r(rep bi_B(2*n))) at 1.
 eapply bi_back;[apply bi_A_pairs|]. rewrite bi_pairs_even.
 eapply bi_back;[apply bi_A_blank|].
 eapply bi_back;[apply bi_D_blocks|]. rewrite bi_blocks_left.
 destruct R as[|[]R].
 - unfold cR;cbn[chd ctl]. apply bi_padR.
   change(bi_hit(cR StD([S1;S0;S1]++rep bi_B(2*n+1))[S0;S1;S0])).
   eapply bi_back;[apply bi_D_010|].
   change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 0++bi_T false++rep bi_B(2*n+1))[])).
   apply bi_D_protected;[apply bi_end|exact I].
 - eapply bi_back;[apply bi_D_010|].
   change(bi_hit(cR StD([S1;S0;S1]++rep bi_B 0++bi_T false++rep bi_B(2*n+1))R)).
   apply bi_D_protected;[apply bi_end|exact HS].
 - contradiction.
Qed.
Theorem bi_return:forall c,bi_mark c->exists d,bi_mark d/\Reach1 tm c d.
Proof.
 intros c H;change(bi_pos c);inversion H;subst.
 - inversion H0;subst.
   + apply bi_terminal_return;assumption.
   + destruct k.
     * apply bi_C_marker_return;assumption.
     * apply bi_C_pairs_return;assumption.
 - apply bi_phase_return;assumption.
Qed.
End Machine.
Lemma bi_mark_instr:forall c,bi_mark c->cinstr c=(StC,S1).
Proof. intros c H;inversion H;reflexivity. Qed.


