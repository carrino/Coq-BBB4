(** S012: the rightmost nonblank of the head/right suffix is 1 in B;
    A may also have an all-blank suffix. A universal one-step invariant
    and finite left/right inductions force arbitrarily late state returns. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition r12_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DR StA
 |StA,S2=>mkTrans S0 DL StA |StA,S3=>mkTrans S0 DL StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S1 DL StB end).
Definition r12_zeros := Forall(fun s=>s=S0).
Inductive r12_marker : list Sym -> Prop :=
 |r12_at : forall r,r12_zeros r->r12_marker(S1::r)
 |r12_skip : forall h r,r12_marker r->r12_marker(h::r).
Definition r12_inv(cc:cconf) := let '(q,(l,h,r)):=cc in
 r12_marker(h::r) \/(q=StA /\r12_zeros(h::r)).
Lemma r12_zero_cons : forall h r,r12_zeros(h::r)->h=S0 /\r12_zeros r.
Proof. intros h r H;inversion H;subst;auto. Qed.
Lemma r12_drop_unmarked : forall h r,h<>S1->r12_marker(h::r)->r12_marker r.
Proof. intros h r H1 H;inversion H;subst;[contradiction|assumption]. Qed.
Lemma r12_split_marker : forall h r,r12_marker(h::r)->r12_marker r \/r12_zeros r.
Proof. intros h r H;inversion H;subst;auto. Qed.
Lemma r12_right_marker : forall r,r12_marker r->r12_marker(chd r::ctl r).
Proof. intros[|h r]H;[inversion H|exact H]. Qed.
Lemma r12_right_zeros : forall r,r12_zeros r->r12_zeros(chd r::ctl r).
Proof. intros[|h r]H;[repeat constructor|exact H]. Qed.
Lemma r12_left_marker : forall l w r,r12_marker r->r12_marker(chd l::w::r).
Proof. intros;apply r12_skip;apply r12_skip;assumption. Qed.
Lemma r12_inv_step : forall cc cc',r12_inv cc->cstep r12_tm cc=Some cc'->r12_inv cc'.
Proof.
 intros[q[[l h]r]]cc' H E;destruct q,h;
 cbn[cstep r12_tm ctape_move]in E;inversion E;subst;clear E;cbn[r12_inv]in *.
 - destruct H as[H|[_ H]].
   + left;apply r12_left_marker;exact(r12_drop_unmarked S0 r ltac:(discriminate)H).
   + left;apply r12_skip;apply r12_at;apply r12_zero_cons in H;tauto.
 - destruct H as[H|[_ H]].
   + apply r12_split_marker in H as[H|H].
     * left;apply r12_right_marker;exact H.
     * right;split;[reflexivity|apply r12_right_zeros;exact H].
   + apply r12_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + left;apply r12_left_marker;exact(r12_drop_unmarked S2 r ltac:(discriminate)H).
   + apply r12_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + left;apply r12_left_marker;exact(r12_drop_unmarked S3 r ltac:(discriminate)H).
   + apply r12_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[H _]];[|discriminate].
   left;apply r12_right_marker;exact(r12_drop_unmarked S0 r ltac:(discriminate)H).
 - destruct H as[H|[H _]];[|discriminate].
   apply r12_split_marker in H as[H|H].
   + left;apply r12_right_marker;exact H.
   + right;split;[reflexivity|apply r12_right_zeros;exact H].
 - destruct H as[H|[H _]];[|discriminate].
   left;apply r12_left_marker;exact(r12_drop_unmarked S2 r ltac:(discriminate)H).
 - destruct H as[H|[H _]];[|discriminate].
   left;apply r12_left_marker;exact(r12_drop_unmarked S3 r ltac:(discriminate)H).
Qed.
Lemma r12_inv_steps : forall n cc cc',r12_inv cc->csteps r12_tm n cc=Some cc'->r12_inv cc'.
Proof.
 induction n;intros cc cc' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep r12_tm cc)as[c1|]eqn:E1;[|discriminate].
   eapply IHn;[eapply r12_inv_step;eauto|exact E].
Qed.
Lemma r12_inv_initial : r12_inv c0.
Proof. right;split;[reflexivity|repeat constructor]. Qed.
Lemma r12_total : Total r12_tm.
Proof. intros q h;unfold r12_tm;eexists;reflexivity. Qed.
Lemma r12_B_nonzero_reaches_A : forall l h r,h=S1 \/h=S2 \/h=S3 ->
 ore_reaches r12_tm StA(StB,(l,h,r)).
Proof.
 induction l as[|x l IH];intros h r[H|[H|H]];subst h.
 - exists 1;eexists;split;reflexivity.
 - exists 6;eexists;split;reflexivity.
 - exists 3;eexists;split;reflexivity.
 - exists 1;eexists;split;reflexivity.
 - destruct x.
   + eapply ore_reaches_step;[reflexivity|].
     eapply ore_reaches_step;[reflexivity|].
     eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
 - destruct x.
   + exists 3;eexists;split;reflexivity.
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
Qed.
Lemma r12_B_reaches_A : forall r l h,r12_marker(h::r)->ore_reaches r12_tm StA(StB,(l,h,r)).
Proof.
 induction r as[|x r IH];intros l h H;destruct h.
 - apply(r12_drop_unmarked S0[]ltac:(discriminate))in H;inversion H.
 - apply r12_B_nonzero_reaches_A;auto.
 - apply r12_B_nonzero_reaches_A;auto.
 - apply r12_B_nonzero_reaches_A;auto.
 - eapply ore_reaches_step;[reflexivity|apply IH].
   exact(r12_drop_unmarked S0(x::r) ltac:(discriminate)H).
 - apply r12_B_nonzero_reaches_A;auto.
 - apply r12_B_nonzero_reaches_A;auto.
 - apply r12_B_nonzero_reaches_A;auto.
Qed.
Lemma r12_reaches_A : forall cc,r12_inv cc->ore_reaches r12_tm StA cc.
Proof.
 intros[q[[l h]r]]H;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - apply r12_B_reaches_A;destruct H as[H|[H _]];[exact H|discriminate].
Qed.
Lemma r12_B_checked : ore_auto_goal r12_tm StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem r12_nonhalt : NonHalt r12_tm.
Proof. apply ore_total_nonhalt;exact r12_total. Qed.
Theorem r12_recurrent : forall goal N,exists n,N<=n /\VisitsAt r12_tm goal n.
Proof.
 intros goal N;destruct goal.
 - destruct(ore_total_csteps r12_tm r12_total N c0)as(cc&Eprefix).
   assert(Hinv:r12_inv cc)by(eapply r12_inv_steps;[exact r12_inv_initial|exact Eprefix]).
   destruct(r12_reaches_A cc Hinv)as(k&cc'&Etail&Hstate).
   exists(N+k);split;[lia|];exists(lift cc');split;[|exact Hstate].
   rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,Eprefix;exact Etail.
 - apply(ore_reaches_recurs r12_tm StB r12_total).
   apply ore_auto_goal_sound;exact r12_B_checked.
Qed.
Theorem r12_state_zero : QHBound 0 r12_tm.
Proof.
 intros q s[_ Hquiet];destruct(r12_recurrent q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Theorem r12_sound : NonHalt r12_tm /\QHBound 0 r12_tm.
Proof. split;[exact r12_nonhalt|exact r12_state_zero]. Qed.
Lemma r12_B0_drift : forall n l,csteps r12_tm n(StB,(l,S0,[]))=Some(StB,(repeat S3 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps r12_tm n(StB,(S3::l,S0,[]))=Some(StB,(S3::(repeat S3 n++l),S0,[]))).
 rewrite IHn.
 assert(E:forall m r0,repeat S3 m++S3::r0=S3::(repeat S3 m++r0)).
 {intro m;induction m;intro r0;cbn;[reflexivity|now rewrite IHm]. }
 now rewrite E.
Qed.
Print Assumptions r12_sound.
