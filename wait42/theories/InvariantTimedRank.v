(** Scalar ranks and potential growth on a reachable invariant.
    No hypothesis is imposed on configurations outside the invariant, and no
    nonhalting premise is needed: a future visit supplies finite continuation. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBBWait42 Require Import Spec.

Section InvariantExecution.
Variable tm : TM.
Variable Inv : ExecState -> Prop.
Hypothesis inv_step : forall c c', Inv c -> step tm c = Some c' -> Inv c'.

Lemma invariant_after_steps : forall n c c',
 Inv c -> stepn tm n c = Some c' -> Inv c'.
Proof.
 induction n as [|n IH]; intros c c' HI Hrun.
 - cbn [stepn] in Hrun; injection Hrun as <-; exact HI.
 - cbn [stepn] in Hrun.
   destruct (step tm c) as [d|] eqn:Hd; [|discriminate].
   eapply IH; [eapply inv_step; eauto|exact Hrun].
Qed.

Section Rank.
Variable q : St.
Variable R : ExecState -> nat.
Hypothesis avoiding_decrease : forall c c',
 Inv c -> step tm c = Some c' -> fst c <> q -> fst c' <> q -> R c' < R c.

Lemma invariant_rank_reach_budget : forall r c,
 Inv c -> R c < r ->
 (exists j cq, stepn tm j c = Some cq /\ fst cq = q) ->
 exists j cq, j <= r /\ stepn tm j c = Some cq /\ fst cq = q.
Proof.
 induction r as [|r IH]; intros c HI Hr Hfuture; [lia|].
 destruct (st_eqb (fst c) q) eqn:Eq.
 - apply st_eqb_spec in Eq; exists 0,c; repeat split; auto; lia.
 - assert (Hneq : fst c <> q).
   { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
   destruct Hfuture as (j & cq & Hrun & Hq).
   destruct j as [|j].
   { cbn [stepn] in Hrun; injection Hrun as <-; contradiction. }
   cbn [stepn] in Hrun.
   destruct (step tm c) as [d|] eqn:Hd; [|discriminate].
   destruct (st_eqb (fst d) q) eqn:Eq'.
   + apply st_eqb_spec in Eq'; exists 1,d; split; [lia|].
     split; [cbn [stepn]; rewrite Hd; reflexivity|exact Eq'].
   + assert (Hneq' : fst d <> q).
     { intro E; apply st_eqb_spec in E; rewrite E in Eq'; discriminate. }
     assert (HId : Inv d) by (eapply inv_step; eauto).
     assert (Hdec : R d < R c) by (eapply avoiding_decrease; eauto).
     destruct (IH d HId ltac:(lia) (ex_intro _ j (ex_intro _ cq (conj Hrun Hq))))
       as (k & ck & Hk & Hsteps & Htarget).
     exists (S k),ck; split; [lia|]; split; [|exact Htarget].
     cbn [stepn]; rewrite Hd; exact Hsteps.
Qed.

Theorem invariant_rank_reach : forall c,
 Inv c -> (exists j cq, stepn tm j c = Some cq /\ fst cq = q) ->
 exists j cq, j <= S (R c) /\ stepn tm j c = Some cq /\ fst cq = q.
Proof. intros c HI HF; eapply invariant_rank_reach_budget; eauto. Qed.

Theorem invariant_rank_beep_window : forall B cB,
 Inv cB -> stepn tm B InitES = Some cB -> FutureBeep tm q B ->
 BeepWindow tm q B (S (R cB)).
Proof.
 intros B cB HI HB (t & Ht & cq & Hrun & Hq).
 replace t with (B+(t-B)) in Hrun by lia; rewrite stepn_add,HB in Hrun.
 destruct (invariant_rank_reach cB HI
   (ex_intro _ (t-B) (ex_intro _ cq (conj Hrun Hq))))
   as (j & d & Hj & Hd & Htarget).
 exists (B+j); repeat split; try lia.
 exists d; split; [rewrite stepn_add,HB; exact Hd|exact Htarget].
Qed.
End Rank.

Section Growth.
Variable G : ExecState -> nat.
Variable K : nat.
Hypothesis potential_growth : forall c c',
 Inv c -> step tm c = Some c' -> G c' <= G c + K.

Lemma invariant_measure_after_steps : forall n c c',
 Inv c -> stepn tm n c = Some c' -> G c' <= G c + K*n.
Proof.
 induction n as [|n IH]; intros c c' HI Hrun.
 - cbn [stepn] in Hrun; injection Hrun as <-; lia.
 - cbn [stepn] in Hrun.
   destruct (step tm c) as [d|] eqn:Hd; [|discriminate].
   assert (HId : Inv d) by (eapply inv_step; eauto).
   specialize (IH d c' HId Hrun).
   pose proof (potential_growth c d HI Hd).
   rewrite Nat.mul_succ_r; lia.
Qed.
End Growth.
End InvariantExecution.

Theorem invariant_rank_potential_beep_window : forall tm (Inv : ExecState -> Prop) q R G K initial a d B,
 Inv InitES ->
 (forall c c', Inv c -> step tm c = Some c' -> Inv c') ->
 (forall c c', Inv c -> step tm c = Some c' -> fst c <> q -> fst c' <> q -> R c' < R c) ->
 (forall c c', Inv c -> step tm c = Some c' -> G c' <= G c + K) ->
 G InitES <= initial ->
 (forall c, Inv c -> R c <= a * G c + d) ->
 FutureBeep tm q B -> BeepWindow tm q B (S (a * (initial + K*B) + d)).
Proof.
 intros tm Inv q R G K initial a d B HI Hclosed Hdec Hgrowth Hinitial Hdom HF.
 destruct HF as (t & Ht & cq & Hrun & Hq).
 destruct (stepn_prefix tm B t InitES cq Ht Hrun) as (cB & HB & Htail).
 assert (HIB : Inv cB) by (exact (invariant_after_steps tm Inv Hclosed B InitES cB HI HB)).
 pose proof (invariant_measure_after_steps tm Inv Hclosed G K Hgrowth
   B InitES cB HI HB) as HG.
 assert (HR : R cB <= a * (initial + K*B) + d).
 { eapply Nat.le_trans; [exact (Hdom cB HIB)|]. nia. }
 assert (HF : FutureBeep tm q B).
 { exists t; split; [exact Ht|exists cq; auto]. }
 destruct (invariant_rank_beep_window tm Inv Hclosed q R Hdec B cB HIB HB HF)
   as (u & HBu & Hub & Huq).
 exists u; repeat split; auto; lia.
Qed.

Corollary invariant_ranks_potential_window_bound : forall tm (Inv : ExecState -> Prop)
 (R : St -> ExecState -> nat) G K initial (a d : St -> nat) B w,
 Inv InitES ->
 (forall c c', Inv c -> step tm c = Some c' -> Inv c') ->
 (forall q c c', Inv c -> step tm c = Some c' -> fst c <> q -> fst c' <> q -> R q c' < R q c) ->
 (forall c c', Inv c -> step tm c = Some c' -> G c' <= G c + K) ->
 G InitES <= initial ->
 (forall q c, Inv c -> R q c <= a q * G c + d q) ->
 (forall q, S (a q * (initial + K*B) + d q) <= w) -> WindowBound tm B w.
Proof.
 intros tm Inv R G K initial a d B w HI Hclosed Hdec Hgrowth Hinitial Hdom Hw q HF.
 destruct (invariant_rank_potential_beep_window tm Inv q (R q) G K initial
   (a q) (d q) B HI Hclosed (Hdec q) Hgrowth Hinitial (Hdom q) HF)
   as (t & Ht & Htw & Htq).
 exists t; repeat split; auto; specialize (Hw q); lia.
Qed.

Module InvariantRegression.
Definition machine : TM := fun q _ => match q with
 | StA => Some (mkTrans S0 DR StB)
 | StB => None
 | StC => Some (mkTrans S0 DR StD)
 | StD => Some (mkTrans S0 DR StD) end.
Definition good (c : ExecState) := fst c = StA \/ fst c = StB.
Definition rank (_ : ExecState) := 0.
Definition potential (c : ExecState) := match fst c with StD => 10 | _ => 0 end.

Lemma good_initial : good InitES.
Proof. left; reflexivity. Qed.
Lemma good_closed : forall c c', good c -> step machine c = Some c' -> good c'.
Proof.
 intros [q tp] c' HI Hstep; unfold good in HI; cbn [fst] in HI; destruct q;
   cbn [step machine] in Hstep; try discriminate; try (solve [intuition discriminate]).
 injection Hstep as <-; right; reflexivity.
Qed.
Lemma rank_decrease : forall c c', good c -> step machine c = Some c' ->
 fst c <> StB -> fst c' <> StB -> rank c' < rank c.
Proof.
 intros [q tp] c' HI Hstep _ Hnot; unfold good in HI; cbn [fst] in HI; destruct q;
   cbn [step machine] in Hstep; try discriminate; try (solve [intuition discriminate]).
 injection Hstep as <-; contradiction.
Qed.
Lemma good_growth : forall c c', good c -> step machine c = Some c' ->
 potential c' <= potential c + 0.
Proof.
 intros [q tp] c' HI Hstep; unfold good in HI; cbn [fst] in HI; destruct q;
   cbn [step machine] in Hstep; try discriminate; try (solve [intuition discriminate]).
 injection Hstep as <-; reflexivity.
Qed.
Lemma rank_dominated : forall c, good c -> rank c <= 3 * potential c + 0.
Proof. intros; unfold rank; lia. Qed.
Example future_target : FutureBeep machine StB 0.
Proof. exists 1; split; [lia|eexists; split; reflexivity]. Qed.
Example invariant_window : BeepWindow machine StB 0 1.
Proof.
 exact (invariant_rank_potential_beep_window machine good StB rank potential
   0 0 3 0 0 good_initial good_closed rank_decrease good_growth
   (Nat.le_refl 0) rank_dominated future_target).
Qed.
Example plus_one_is_needed : ~ BeepWindow machine StB 0 0.
Proof.
 intros (t & Ht & Hb & c & Hrun & Hq); assert (t=0) by lia; subst t.
 cbn [stepn] in Hrun; injection Hrun as <-; discriminate.
Qed.
Example no_nonhalt_premise : ~ NonHalt machine.
Proof. intro H; apply (H 2); reflexivity. Qed.
Example global_descent_is_false : ~ (forall c c', step machine c = Some c' ->
 fst c <> StB -> fst c' <> StB -> rank c' < rank c).
Proof.
 intro H; specialize (H (StD,snd InitES) _ eq_refl ltac:(discriminate) ltac:(discriminate)).
 unfold rank in H; lia.
Qed.
Example global_growth_is_false : ~ (forall c c', step machine c = Some c' ->
 potential c' <= potential c + 0).
Proof.
 intro H; specialize (H (StC,snd InitES) _ eq_refl).
 change (10 <= 0) in H; lia.
Qed.
End InvariantRegression.

Print Assumptions invariant_rank_potential_beep_window.
Print Assumptions invariant_ranks_potential_window_bound.

Section CompactInvariantExecution.
Variable tm : TM.
Variable Inv : cconf -> Prop.
Hypothesis inv_step : forall c c', Inv c -> cstep tm c = Some c' -> Inv c'.

Lemma c_invariant_after_steps : forall n c c',
 Inv c -> csteps tm n c = Some c' -> Inv c'.
Proof.
 induction n as [|n IH]; intros c c' HI Hrun.
 - cbn [csteps] in Hrun; injection Hrun as <-; exact HI.
 - cbn [csteps] in Hrun.
   destruct (cstep tm c) as [d|] eqn:Hd; [|discriminate].
   eapply IH; [eapply inv_step; eauto|exact Hrun].
Qed.

Section Rank.
Variable q : St.
Variable R : cconf -> nat.
Hypothesis avoiding_decrease : forall c c',
 Inv c -> cstep tm c = Some c' -> fst c <> q -> fst c' <> q -> R c' < R c.

Lemma c_invariant_rank_reach_budget : forall r c,
 Inv c -> R c < r ->
 (exists j cq, csteps tm j c = Some cq /\ fst cq = q) ->
 exists j cq, j <= r /\ csteps tm j c = Some cq /\ fst cq = q.
Proof.
 induction r as [|r IH]; intros c HI Hr Hfuture; [lia|].
 destruct (st_eqb (fst c) q) eqn:Eq.
 - apply st_eqb_spec in Eq; exists 0,c; repeat split; auto; lia.
 - assert (Hneq : fst c <> q).
   { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
   destruct Hfuture as (j & cq & Hrun & Hq).
   destruct j as [|j].
   { cbn [csteps] in Hrun; injection Hrun as <-; contradiction. }
   cbn [csteps] in Hrun.
   destruct (cstep tm c) as [d|] eqn:Hd; [|discriminate].
   destruct (st_eqb (fst d) q) eqn:Eq'.
   + apply st_eqb_spec in Eq'; exists 1,d; split; [lia|].
     split; [cbn [csteps]; rewrite Hd; reflexivity|exact Eq'].
   + assert (Hneq' : fst d <> q).
     { intro E; apply st_eqb_spec in E; rewrite E in Eq'; discriminate. }
     assert (HId : Inv d) by (eapply inv_step; eauto).
     assert (Hdec : R d < R c) by (eapply avoiding_decrease; eauto).
     destruct (IH d HId ltac:(lia) (ex_intro _ j (ex_intro _ cq (conj Hrun Hq))))
       as (k & ck & Hk & Hsteps & Htarget).
     exists (S k),ck; split; [lia|]; split; [|exact Htarget].
     cbn [csteps]; rewrite Hd; exact Hsteps.
Qed.

Theorem c_invariant_rank_reach : forall c,
 Inv c -> (exists j cq, csteps tm j c = Some cq /\ fst cq = q) ->
 exists j cq, j <= S (R c) /\ csteps tm j c = Some cq /\ fst cq = q.
Proof. intros c HI HF; eapply c_invariant_rank_reach_budget; eauto. Qed.

End Rank.

Section Growth.
Variable G : cconf -> nat.
Variable K : nat.
Hypothesis potential_growth : forall c c',
 Inv c -> cstep tm c = Some c' -> G c' <= G c + K.

Lemma c_invariant_measure_after_steps : forall n c c',
 Inv c -> csteps tm n c = Some c' -> G c' <= G c + K*n.
Proof.
 induction n as [|n IH]; intros c c' HI Hrun.
 - cbn [csteps] in Hrun; injection Hrun as <-; lia.
 - cbn [csteps] in Hrun.
   destruct (cstep tm c) as [d|] eqn:Hd; [|discriminate].
   assert (HId : Inv d) by (eapply inv_step; eauto).
   specialize (IH d c' HId Hrun).
   pose proof (potential_growth c d HI Hd).
   rewrite Nat.mul_succ_r; lia.
Qed.
End Growth.
End CompactInvariantExecution.

Theorem c_invariant_rank_potential_beep_window : forall tm (Inv : cconf -> Prop)
 q R G K initial a d anchor seed B,
 csteps tm anchor c0 = Some seed -> Inv seed -> anchor <= B ->
 (forall c c', Inv c -> cstep tm c = Some c' -> Inv c') ->
 (forall c c', Inv c -> cstep tm c = Some c' -> fst c <> q -> fst c' <> q -> R c' < R c) ->
 (forall c c', Inv c -> cstep tm c = Some c' -> G c' <= G c + K) ->
 G seed <= initial ->
 (forall c, Inv c -> R c <= a * G c + d) ->
 FutureBeep tm q B ->
 BeepWindow tm q B (S (a * (initial + K*(B-anchor)) + d)).
Proof.
 intros tm Inv q R G K initial a d anchor seed B HA HI HAB Hclosed Hdec HG HI0 Hdom
   (t & Ht & cq & Hrun & Hq).
 destruct (stepn_csteps tm t cq Hrun) as (ct & Hct & Hlift).
 rewrite <- Hlift in Hq.
 assert (Htarget : fst ct = q).
 { destruct ct as [qs [[ls hs] rs]]; exact Hq. }
 replace t with (anchor+(t-anchor)) in Hct by lia.
 rewrite csteps_add,HA in Hct.
 destruct (csteps_prefix tm (B-anchor) (t-anchor) seed ct ltac:(lia) Hct)
   as (cB & HB & Htail).
 assert (HIB : Inv cB).
 { exact (c_invariant_after_steps tm Inv Hclosed (B-anchor) seed cB HI HB). }
 pose proof (c_invariant_measure_after_steps tm Inv Hclosed G K HG
   (B-anchor) seed cB HI HB) as Hgrowth.
 assert (HR : R cB <= a * (initial + K*(B-anchor)) + d).
 { eapply Nat.le_trans; [exact (Hdom cB HIB)|]; nia. }
 destruct (c_invariant_rank_reach tm Inv Hclosed q R Hdec cB HIB
   (ex_intro _ _ (ex_intro _ ct (conj Htail Htarget))))
   as (j & cd & Hj & Hsteps & Hcd).
 assert (HrunB : csteps tm B c0 = Some cB).
 { replace B with (anchor+(B-anchor)) by lia; rewrite csteps_add,HA; exact HB. }
 exists (B+j); repeat split; try lia.
 exists (lift cd); split.
 - rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add,HrunB; exact Hsteps.
 - destruct cd as [qs [[ls hs] rs]]; exact Hcd.
Qed.

Corollary c_invariant_ranks_potential_window_bound : forall tm (Inv : cconf -> Prop)
 (R : St -> cconf -> nat) G K initial (a d : St -> nat) anchor seed B w,
 csteps tm anchor c0 = Some seed -> Inv seed -> anchor <= B ->
 (forall c c', Inv c -> cstep tm c = Some c' -> Inv c') ->
 (forall q c c', Inv c -> cstep tm c = Some c' -> fst c <> q -> fst c' <> q -> R q c' < R q c) ->
 (forall c c', Inv c -> cstep tm c = Some c' -> G c' <= G c + K) ->
 G seed <= initial -> (forall q c, Inv c -> R q c <= a q * G c + d q) ->
 (forall q, S (a q * (initial + K*(B-anchor)) + d q) <= w) -> WindowBound tm B w.
Proof.
 intros tm Inv R G K initial a d anchor seed B w HA HI HAB HC HD HG HI0 Hdom Hw q HF.
 destruct (c_invariant_rank_potential_beep_window tm Inv q (R q) G K initial
   (a q) (d q) anchor seed B HA HI HAB HC (HD q) HG HI0 (Hdom q) HF)
   as (t & Ht & Htw & Htq).
 exists t; repeat split; auto; specialize (Hw q); lia.
Qed.

Print Assumptions c_invariant_rank_potential_beep_window.
Print Assumptions c_invariant_ranks_potential_window_bound.

(** Inactive targets require no rank: a reachable tail invariant excludes
    them directly. This is essential for a tail using only C and D. *)
Lemma c_invariant_future_target : forall tm (Inv : cconf -> Prop) anchor seed B
 (targets : St -> Prop),
 csteps tm anchor c0 = Some seed -> Inv seed -> anchor <= B ->
 (forall c c', Inv c -> cstep tm c = Some c' -> Inv c') ->
 (forall c, Inv c -> targets (fst c)) ->
 forall q, FutureBeep tm q B -> targets q.
Proof.
 intros tm Inv anchor seed B targets HA HI HAB HC HT q
   (t & Ht & cq & Hrun & Hq).
 destruct (stepn_csteps tm t cq Hrun) as (ct & Hct & Hlift).
 replace t with (anchor+(t-anchor)) in Hct by lia.
 rewrite csteps_add,HA in Hct.
 pose proof (c_invariant_after_steps tm Inv HC (t-anchor) seed ct HI Hct) as HIt.
 specialize (HT ct HIt); rewrite <- Hlift in Hq.
 assert (Hstate : fst ct = q).
 { destruct ct as [qs [[ls hs] rs]]; exact Hq. }
 now rewrite Hstate in HT.
Qed.

Corollary c_invariant_active_ranks_window_bound : forall tm (Inv : cconf -> Prop)
 (targets : St -> Prop) (R : St -> cconf -> nat) G K initial
 (a d : St -> nat) anchor seed B w,
 csteps tm anchor c0 = Some seed -> Inv seed -> anchor <= B ->
 (forall c c', Inv c -> cstep tm c = Some c' -> Inv c') ->
 (forall c, Inv c -> targets (fst c)) ->
 (forall q, targets q -> forall c c', Inv c -> cstep tm c = Some c' ->
   fst c <> q -> fst c' <> q -> R q c' < R q c) ->
 (forall c c', Inv c -> cstep tm c = Some c' -> G c' <= G c + K) ->
 G seed <= initial ->
 (forall q, targets q -> forall c, Inv c -> R q c <= a q * G c + d q) ->
 (forall q, targets q -> S (a q * (initial + K*(B-anchor)) + d q) <= w) ->
 WindowBound tm B w.
Proof.
 intros tm Inv targets R G K initial a d anchor seed B w HA HI HAB HC HT HD HG HI0 Hdom Hw q HF.
 pose proof (c_invariant_future_target tm Inv anchor seed B targets HA HI HAB HC HT q HF) as Hq.
 destruct (c_invariant_rank_potential_beep_window tm Inv q (R q) G K initial
   (a q) (d q) anchor seed B HA HI HAB HC (HD q Hq) HG HI0 (Hdom q Hq) HF)
   as (t & Ht & Htw & Htq).
 exists t; repeat split; auto; specialize (Hw q Hq); lia.
Qed.

Print Assumptions c_invariant_active_ranks_window_bound.
