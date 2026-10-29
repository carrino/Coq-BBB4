(** A state-only marker family for the remaining two B3 branch roots.
    The B2 write is arbitrary. B3 either exits to A, moves right, or
    moves left while writing 1/2. All these cases visit both states
    infinitely often from blank. No instruction recurrence is asserted. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
 OneStateReach StateOnlyCloseout RightMarkerState.
Import ListNotations.

Definition mrf_tm (b2:Sym)(b3:Trans)(q:St)(h:Sym) : option Trans := Some
 (match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S0 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S1 DR StA
 |StB,S2=>mkTrans b2 DL StA |StB,S3=>b3
 end).
Definition mrf_check b3 := st_eqb(t_next b3)StA ||
 match t_dir b3 with DR=>true |DL=>sym_eqb(t_write b3)S1 || sym_eqb(t_write b3)S2 end.

Lemma mrf_inv_step : forall b2 b3 cc cc',
 mr_inv cc -> cstep(mrf_tm b2 b3)cc=Some cc' -> mr_inv cc'.
Proof.
 intros b2 [w d next] [q[[l h]r]] cc' H E. destruct q,h;
 cbn[cstep mrf_tm ctape_move]in E.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[_ H]].
   + left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + left;apply mr_skip;apply mr_at. apply mr_zero_cons in H;tauto.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[_ H]].
   + apply mr_split_one in H as[H|H].
     * left;apply mr_right_marker;exact H.
     * right;split;[reflexivity|apply mr_right_zeros;exact H].
   + apply mr_zero_cons in H as[H _];discriminate.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[_ H]].
   + left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + apply mr_zero_cons in H as[H _];discriminate.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[_ H]].
   + left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + apply mr_zero_cons in H as[H _];discriminate.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[H _]];[|discriminate].
   left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[H _]];[|discriminate].
   apply mr_split_one in H as[H|H].
   + left;apply mr_right_marker;exact H.
   + right;split;[reflexivity|apply mr_right_zeros;exact H].
 - inversion E;subst;clear E;cbn[mr_inv]in *.
   destruct H as[H|[H _]];[|discriminate].
   left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
 - destruct d;inversion E;subst;clear E;cbn[mr_inv]in *;
   destruct H as[H|[H _]];try discriminate.
   + left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
Qed.
Lemma mrf_inv_steps : forall b2 b3 n cc cc',
 mr_inv cc -> csteps(mrf_tm b2 b3)n cc=Some cc' -> mr_inv cc'.
Proof.
 intros b2 b3 n;induction n;intros cc cc' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep(mrf_tm b2 b3)cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[eapply mrf_inv_step;eauto|exact E].
Qed.
Lemma mrf_total : forall b2 b3, Total(mrf_tm b2 b3).
Proof. intros b2 b3 q h;unfold mrf_tm;eexists;reflexivity. Qed.

Lemma mrf_marker_exit : forall b2 b3 l h r,
 h=S1 \/ h=S2 -> ore_reaches(mrf_tm b2 b3)StA(StB,(l,h,r)).
Proof.
 intros b2 b3 l h r [-> | ->];eapply ore_reaches_step;[reflexivity| |reflexivity|];
 exists 0;eexists;split;reflexivity.
Qed.
Lemma mrf_blank_return : forall b2 v l r,
 v=S1 \/ v=S2 ->
 ore_reaches(mrf_tm b2(mkTrans v DL StB))StA(StB,(l,S0,v::r)).
Proof.
 intros b2 v l r Hv. eapply ore_reaches_step;[reflexivity|].
 apply mrf_marker_exit;exact Hv.
Qed.
Lemma mrf_left_sweep : forall b2 v,
 v=S1 \/ v=S2 -> forall l r,
 ore_reaches(mrf_tm b2(mkTrans v DL StB))StA(StB,(l,S3,r)).
Proof.
 intros b2 v Hv l;induction l as[|x l IH];intro r.
 - eapply ore_reaches_step;[reflexivity|]. apply mrf_blank_return;exact Hv.
 - eapply ore_reaches_step;[reflexivity|]. destruct x.
   + apply mrf_blank_return;exact Hv.
   + apply mrf_marker_exit;auto.
   + apply mrf_marker_exit;auto.
   + apply IH.
Qed.
Lemma mrf_B_reaches_A : forall b2 b3,
 mrf_check b3=true -> forall r l h,
 mr_marker(h::r) -> ore_reaches(mrf_tm b2 b3)StA(StB,(l,h,r)).
Proof.
 intros b2 [w d next] Hgood r;induction r as[|x r IH];intros l h H;destruct h.
 - apply(mr_drop_nonone S0 [] ltac:(discriminate))in H;inversion H.
 - apply mrf_marker_exit;auto.
 - apply mrf_marker_exit;auto.
 - apply(mr_drop_nonone S3 [] ltac:(discriminate))in H;inversion H.
 - eapply ore_reaches_step;[reflexivity|]. apply IH.
   eapply mr_drop_nonone;[|exact H];discriminate.
 - apply mrf_marker_exit;auto.
 - apply mrf_marker_exit;auto.
 - destruct next.
   + destruct d;eapply ore_reaches_step;[reflexivity| |reflexivity|];
     exists 0;eexists;split;reflexivity.
   + destruct d.
     * apply mrf_left_sweep. change ((sym_eqb w S1 || sym_eqb w S2)=true) in Hgood.
       apply orb_true_iff in Hgood as[Hgood|Hgood];
       apply sym_eqb_spec in Hgood;auto.
     * eapply ore_reaches_step;[reflexivity|]. apply IH.
       eapply mr_drop_nonone;[|exact H];discriminate.
Qed.
Lemma mrf_reaches_A : forall b2 b3,
 mrf_check b3=true -> forall cc,mr_inv cc -> ore_reaches(mrf_tm b2 b3)StA cc.
Proof.
 intros b2 b3 Hgood[q[[l h]r]]H;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - apply mrf_B_reaches_A;[exact Hgood|]. destruct H as[H|[H _]];[exact H|discriminate].
Qed.
Lemma mrf_B_check : forall b2 b3, ore_auto_goal(mrf_tm b2 b3)StB=true.
Proof. intros;vm_compute;reflexivity. Qed.
Lemma mrf_recurrent : forall b2 b3,
 mrf_check b3=true -> forall goal N,exists n,N<=n /\ VisitsAt(mrf_tm b2 b3)goal n.
Proof.
 intros b2 b3 Hgood goal N;destruct goal.
 - destruct(ore_total_csteps _ (mrf_total b2 b3) N c0)as(cc&Eprefix).
   assert(Hinv:mr_inv cc)by(eapply mrf_inv_steps;[exact mr_inv_initial|exact Eprefix]).
   destruct(mrf_reaches_A b2 b3 Hgood cc Hinv)as(k&cc'&Etail&Hstate).
   exists(N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
   rewrite <-lift_c0. apply csteps_lift. rewrite csteps_add,Eprefix;exact Etail.
 - apply(ore_reaches_recurs _ StB (mrf_total b2 b3)).
   apply ore_auto_goal_sound;apply mrf_B_check.
Qed.
Theorem mrf_nonhalt : forall b2 b3,NonHalt(mrf_tm b2 b3).
Proof. intros;apply ore_total_nonhalt;apply mrf_total. Qed.
Theorem mrf_state_zero : forall b2 b3,mrf_check b3=true -> QHBound 0(mrf_tm b2 b3).
Proof.
 intros b2 b3 Hgood q s [_ Hquiet].
 destruct(mrf_recurrent b2 b3 Hgood q (S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Theorem mrf_completion_state : forall b2 b3,
 mrf_check b3=true -> forall tm,TM_le(mrf_tm b2 b3)tm -> QHBound 0 tm.
Proof.
 intros b2 b3 Hgood tm Hle. eapply state_bound_extend;
 [apply mrf_nonhalt|apply mrf_state_zero;exact Hgood|exact Hle].
Qed.
Theorem mrf_board_state : forall b2 b3,
 mrf_check b3=true -> StateBoardSound 0[mrf_tm b2 b3].
Proof.
 intros b2 b3 Hgood family[<-|Hfalse]tm Hle;
 [eapply mrf_completion_state;eauto|contradiction].
Qed.
Example mrf_excludes_zero_left_B : mrf_check(mkTrans S0 DL StB)=false.
Proof. reflexivity. Qed.
Example mrf_excludes_three_left_B : mrf_check(mkTrans S3 DL StB)=false.
Proof. reflexivity. Qed.
Example mrf_accepts_two_left_B : mrf_check(mkTrans S2 DL StB)=true.
Proof. reflexivity. Qed.
Print Assumptions mrf_state_zero.
