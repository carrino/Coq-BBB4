(** A rightmost1or3 marker prevents B from escaping. B1 need not enter A
    immediately: it writes3 to the right and continues left. Finite left
    induction handles that return, including B2's zero/one bounce. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition rr_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S0 DR StA end).
Definition rr_zeros := Forall(fun s=>s=S0).
Inductive rr_marker : list Sym -> Prop :=
 |rr_at : forall h r,(h=S1 \/ h=S3)->rr_zeros r->rr_marker(h::r)
 |rr_skip : forall h r,rr_marker r->rr_marker(h::r).
Definition rr_inv(cc:cconf) := let '(q,(l,h,r)):=cc in
 rr_marker(h::r) \/(q=StA /\rr_zeros(h::r)).
Lemma rr_zero_cons : forall h r,rr_zeros(h::r)->h=S0 /\rr_zeros r.
Proof. intros h r H;inversion H;subst;auto. Qed.
Lemma rr_drop_unmarked : forall h r,h<>S1->h<>S3->rr_marker(h::r)->rr_marker r.
Proof. intros h r H1 H3 H;inversion H;subst;[tauto|assumption]. Qed.
Lemma rr_split_marker : forall h r,rr_marker(h::r)->rr_marker r \/rr_zeros r.
Proof. intros h r H;inversion H;subst;auto. Qed.
Lemma rr_right_marker : forall r,rr_marker r->rr_marker(chd r::ctl r).
Proof. intros[|h r]H;[inversion H|exact H]. Qed.
Lemma rr_right_zeros : forall r,rr_zeros r->rr_zeros(chd r::ctl r).
Proof. intros[|h r]H;[repeat constructor|exact H]. Qed.
Lemma rr_left_marker : forall l w r,rr_marker r->rr_marker(chd l::w::r).
Proof. intros;apply rr_skip;apply rr_skip;assumption. Qed.
Lemma rr_inv_step : forall cc cc',rr_inv cc->cstep rr_tm cc=Some cc'->rr_inv cc'.
Proof.
 intros[q[[l h]r]]cc' H E;destruct q,h;
 cbn[cstep rr_tm ctape_move]in E;inversion E;subst;clear E;cbn[rr_inv]in *.
 - destruct H as[H|[_ H]].
   + left;apply rr_left_marker;exact(rr_drop_unmarked S0 r ltac:(discriminate)ltac:(discriminate)H).
   + left;apply rr_skip;apply rr_at;[left;reflexivity|apply rr_zero_cons in H;tauto].
 - destruct H as[H|[_ H]].
   + apply rr_split_marker in H as[H|H].
     * left;apply rr_right_marker;exact H.
     * right;split;[reflexivity|apply rr_right_zeros;exact H].
   + apply rr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + left;apply rr_left_marker;exact(rr_drop_unmarked S2 r ltac:(discriminate)ltac:(discriminate)H).
   + apply rr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[_ H]].
   + apply rr_split_marker in H as[H|H].
     * left;apply rr_right_marker;exact H.
     * right;split;[reflexivity|apply rr_right_zeros;exact H].
   + apply rr_zero_cons in H as[H _];discriminate.
 - destruct H as[H|[H _]];[|discriminate].
   left;apply rr_right_marker;exact(rr_drop_unmarked S0 r ltac:(discriminate)ltac:(discriminate)H).
 - destruct H as[H|[H _]];[|discriminate].
   apply rr_split_marker in H as[H|H].
   + left;apply rr_left_marker;exact H.
   + left;apply rr_skip;apply rr_at;[right;reflexivity|exact H].
 - destruct H as[H|[H _]];[|discriminate].
   left;apply rr_left_marker;exact(rr_drop_unmarked S2 r ltac:(discriminate)ltac:(discriminate)H).
 - destruct H as[H|[H _]];[|discriminate].
   apply rr_split_marker in H as[H|H].
   + left;apply rr_right_marker;exact H.
   + right;split;[reflexivity|apply rr_right_zeros;exact H].
Qed.
Lemma rr_inv_steps : forall n cc cc',rr_inv cc->csteps rr_tm n cc=Some cc'->rr_inv cc'.
Proof.
 induction n;intros cc cc' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep rr_tm cc)as[c1|]eqn:E1;[|discriminate].
   eapply IHn;[eapply rr_inv_step;eauto|exact E].
Qed.
Lemma rr_inv_initial : rr_inv c0.
Proof. right;split;[reflexivity|repeat constructor]. Qed.
Lemma rr_total : Total rr_tm.
Proof. intros q h;unfold rr_tm;eexists;reflexivity. Qed.
Lemma rr_B_nonzero_reaches_A : forall l h r,h=S1 \/h=S2 \/h=S3 ->
 ore_reaches rr_tm StA(StB,(l,h,r)).
Proof.
 induction l as[|x l IH];intros h r[H|[H|H]];subst h.
 - exists 3;eexists;split;reflexivity.
 - exists 6;eexists;split;reflexivity.
 - exists 1;eexists;split;reflexivity.
 - destruct x.
   + exists 3;eexists;split;reflexivity.
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
 - destruct x.
   + eapply ore_reaches_step;[reflexivity|].
     eapply ore_reaches_step;[reflexivity|].
     eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
   + eapply ore_reaches_step;[reflexivity|apply IH;auto].
 - exists 1;eexists;split;reflexivity.
Qed.
Lemma rr_B_reaches_A : forall r l h,rr_marker(h::r)->ore_reaches rr_tm StA(StB,(l,h,r)).
Proof.
 induction r as[|x r IH];intros l h H;destruct h.
 - apply(rr_drop_unmarked S0[]ltac:(discriminate)ltac:(discriminate))in H;inversion H.
 - apply rr_B_nonzero_reaches_A;auto.
 - apply rr_B_nonzero_reaches_A;auto.
 - apply rr_B_nonzero_reaches_A;auto.
 - eapply ore_reaches_step;[reflexivity|apply IH].
   exact(rr_drop_unmarked S0(x::r) ltac:(discriminate)ltac:(discriminate)H).
 - apply rr_B_nonzero_reaches_A;auto.
 - apply rr_B_nonzero_reaches_A;auto.
 - apply rr_B_nonzero_reaches_A;auto.
Qed.
Lemma rr_reaches_A : forall cc,rr_inv cc->ore_reaches rr_tm StA cc.
Proof.
 intros[q[[l h]r]]H;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - apply rr_B_reaches_A;destruct H as[H|[H _]];[exact H|discriminate].
Qed.
Lemma rr_B_checked : ore_auto_goal rr_tm StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem rr_nonhalt : NonHalt rr_tm.
Proof. apply ore_total_nonhalt;exact rr_total. Qed.
Theorem rr_recurrent : forall goal N,exists n,N<=n /\VisitsAt rr_tm goal n.
Proof.
 intros goal N;destruct goal.
 - destruct(ore_total_csteps rr_tm rr_total N c0)as(cc&Eprefix).
   assert(Hinv:rr_inv cc)by(eapply rr_inv_steps;[exact rr_inv_initial|exact Eprefix]).
   destruct(rr_reaches_A cc Hinv)as(k&cc'&Etail&Hstate).
   exists(N+k);split;[lia|];exists(lift cc');split;[|exact Hstate].
   rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,Eprefix;exact Etail.
 - apply(ore_reaches_recurs rr_tm StB rr_total).
   apply ore_auto_goal_sound;exact rr_B_checked.
Qed.
Theorem rr_state_zero : QHBound 0 rr_tm.
Proof.
 intros q s[_ Hquiet];destruct(rr_recurrent q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Theorem rr_sound : NonHalt rr_tm /\QHBound 0 rr_tm.
Proof. split;[exact rr_nonhalt|exact rr_state_zero]. Qed.
Lemma rr_B0_drift : forall n l,csteps rr_tm n(StB,(l,S0,[]))=Some(StB,(repeat S1 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps rr_tm n(StB,(S1::l,S0,[]))=Some(StB,(S1::(repeat S1 n++l),S0,[]))).
 rewrite IHn.
 assert(E:forall m r0,repeat S1 m++S1::r0=S1::(repeat S1 m++r0)).
 {intro m;induction m;intro r0;cbn;[reflexivity|now rewrite IHm]. }
 now rewrite E.
Qed.
Print Assumptions rr_sound.
