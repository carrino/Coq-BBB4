(** State recurrence for the branch child [1LB2RA0LB0RB_3RB3RA0LA0RA].
    Its rightmost nonzero symbol on the head/right suffix is 1, unless
    the machine is in A with an entirely blank head/right suffix. Thus
    B's blank sweep must encounter a nonzero symbol and return to A.
    This theorem makes no instruction-recurrence claim. *)
From Coq Require Import List Arith Lia FunctionalExtensionality NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
 OneStateReach StatePipeline StateOnlyCloseout Pipeline.
Import ListNotations.

Definition mr_tm (_q:St) (_h:Sym) : option Trans := Some
 (match _q,_h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S0 DL StA |StB,S3=>mkTrans S0 DR StA
 end).
Definition mr_zeros := Forall(fun s=>s=S0).
Inductive mr_marker : list Sym -> Prop :=
 | mr_at : forall r, mr_zeros r -> mr_marker(S1::r)
 | mr_skip : forall h r, mr_marker r -> mr_marker(h::r).
Definition mr_inv (cc:cconf) := let '(q,(l,h,r)):=cc in
 mr_marker(h::r) \/ (q=StA /\ mr_zeros(h::r)).

Lemma mr_zero_cons : forall h r, mr_zeros(h::r) -> h=S0 /\ mr_zeros r.
Proof. intros h r H; inversion H;subst;auto. Qed.
Lemma mr_drop_nonone : forall h r, h<>S1 -> mr_marker(h::r) -> mr_marker r.
Proof. intros h r Hh H; inversion H;subst;[contradiction|assumption]. Qed.
Lemma mr_split_one : forall r, mr_marker(S1::r) -> mr_marker r \/ mr_zeros r.
Proof. intros r H;inversion H;subst;auto. Qed.
Lemma mr_right_marker : forall r, mr_marker r -> mr_marker(chd r::ctl r).
Proof. intros [|h r] H;[inversion H|exact H]. Qed.
Lemma mr_right_zeros : forall r, mr_zeros r -> mr_zeros(chd r::ctl r).
Proof. intros [|h r] H;[repeat constructor|exact H]. Qed.
Lemma mr_left_marker : forall l w r, mr_marker r -> mr_marker(chd l::w::r).
Proof. intros;apply mr_skip;apply mr_skip;assumption. Qed.

Lemma mr_inv_step : forall cc cc',
 mr_inv cc -> cstep mr_tm cc=Some cc' -> mr_inv cc'.
Proof.
 intros [q[[l h]r]] cc' H E. destruct q,h;
 cbn [cstep mr_tm ctape_move] in E;inversion E;subst;clear E;
 cbn [mr_inv] in *.
 - destruct H as[H|[_ H]].
   + left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + left;apply mr_skip;apply mr_at. apply mr_zero_cons in H;tauto.
 - destruct H as[H|[_ H]].
   + apply mr_split_one in H as[H|H].
     * left;apply mr_right_marker;exact H.
     * right;split;[reflexivity|apply mr_right_zeros;exact H].
   + apply mr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + apply mr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
   + apply mr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[H _]];[|discriminate].
   left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
 - destruct H as[H|[H _]];[|discriminate].
   apply mr_split_one in H as[H|H].
   + left;apply mr_right_marker;exact H.
   + right;split;[reflexivity|apply mr_right_zeros;exact H].
 - destruct H as[H|[H _]];[|discriminate].
   left;apply mr_left_marker. eapply mr_drop_nonone;[|exact H];discriminate.
 - destruct H as[H|[H _]];[|discriminate].
   left;apply mr_right_marker. eapply mr_drop_nonone;[|exact H];discriminate.
Qed.
Lemma mr_inv_steps : forall n cc cc',
 mr_inv cc -> csteps mr_tm n cc=Some cc' -> mr_inv cc'.
Proof.
 induction n;intros cc cc' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep mr_tm cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[eapply mr_inv_step;eauto|exact E].
Qed.
Lemma mr_inv_initial : mr_inv c0.
Proof. right;split;[reflexivity|repeat constructor]. Qed.
Lemma mr_total : Total mr_tm.
Proof. intros q h;unfold mr_tm;eexists;reflexivity. Qed.

Lemma mr_B_reaches_A : forall r l h,
 mr_marker(h::r) -> ore_reaches mr_tm StA (StB,(l,h,r)).
Proof.
 induction r as[|x r IH];intros l h H;destruct h.
 - apply (mr_drop_nonone S0 [] ltac:(discriminate)) in H;inversion H.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
 - eapply ore_reaches_step;[reflexivity|]. apply IH.
   eapply mr_drop_nonone;[|exact H];discriminate.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
 - eapply ore_reaches_step;[reflexivity|]. exists 0;eexists;split;reflexivity.
Qed.
Lemma mr_reaches_A : forall cc, mr_inv cc -> ore_reaches mr_tm StA cc.
Proof.
 intros [q[[l h]r]] H. destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - apply mr_B_reaches_A. destruct H as[H|[H _]];[exact H|discriminate].
Qed.
Lemma mr_B_check : ore_auto_goal mr_tm StB=true.
Proof. vm_compute;reflexivity. Qed.
Lemma mr_recurrent : forall goal N, exists n,N<=n /\ VisitsAt mr_tm goal n.
Proof.
 intros goal N. destruct goal.
 - destruct(ore_total_csteps mr_tm mr_total N c0)as(cc&Eprefix).
   assert(Hinv:mr_inv cc)by(eapply mr_inv_steps;[exact mr_inv_initial|exact Eprefix]).
   destruct(mr_reaches_A cc Hinv)as(k&cc'&Etail&Hstate).
   exists(N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
   rewrite <-lift_c0. apply csteps_lift. rewrite csteps_add,Eprefix;exact Etail.
 - apply(ore_reaches_recurs mr_tm StB mr_total).
   apply ore_auto_goal_sound;exact mr_B_check.
Qed.
Theorem mr_nonhalt : NonHalt mr_tm.
Proof. apply ore_total_nonhalt;exact mr_total. Qed.
Theorem mr_state_zero : QHBound 0 mr_tm.
Proof.
 intros q s [_ Hquiet]. destruct(mr_recurrent q (S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Lemma mr_codes : mr_tm=machine_of_codes [5;10;1;3;15;14;0;2].
Proof.
 apply functional_extensionality;intro q;apply functional_extensionality;intro h.
 destruct q,h;vm_compute;reflexivity.
Qed.
Print Assumptions mr_state_zero.

Definition mr_child := machine_of_codes [5;10;1;3;15;14;0;2].
Theorem mr_child_state_zero : QHBound 0 mr_child.
Proof. unfold mr_child;rewrite <-mr_codes;exact mr_state_zero. Qed.
Theorem mr_child_nonhalt : NonHalt mr_child.
Proof. unfold mr_child;rewrite <-mr_codes;exact mr_nonhalt. Qed.
Theorem mr_child_completion_state : forall tm, TM_le mr_child tm -> QHBound 0 tm.
Proof.
 intros tm Hle. eapply state_bound_extend;
 [exact mr_child_nonhalt|exact mr_child_state_zero|exact Hle].
Qed.
Theorem mr_child_board_state : StateBoardSound 0 [mr_child].
Proof.
 intros family [<-|Hfalse] tm Hle;[apply mr_child_completion_state;exact Hle|contradiction].
Qed.
Print Assumptions mr_child_completion_state.
