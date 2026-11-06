(** Quantitative directional sweeps from the blank tape. *)
From Coq Require Import Arith Lia Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH Deferred_Defs.
From BBBWait42 Require Import Spec Transport.

Definition blank_radius (tp : Tape) (r : nat) : Prop :=
  forall k, r <= k -> t_left tp k = S0 /\ t_right tp k = S0.

Lemma blank_radius_move : forall tp r d w,
  blank_radius tp r -> blank_radius (tape_move d w tp) (S r).
Proof.
  intros tp r d w H k Hk. destruct k as [|k]; [lia|].
  unfold tape_move; destruct d; cbn [t_left t_right push_side tail_side].
  - split; [apply (proj1 (H (S (S k)) ltac:(lia)))|apply (proj2 (H k ltac:(lia)))].
  - split; [apply (proj1 (H k ltac:(lia)))|apply (proj2 (H (S (S k)) ltac:(lia)))].
Qed.

Lemma blank_radius_run : forall tm n c c' r,
  blank_radius (snd c) r -> stepn tm n c = Some c' ->
  blank_radius (snd c') (r+n).
Proof.
  intros tm n; induction n as [|n IH]; intros [q tp] c' r Hblank Hrun.
  - cbn [stepn] in Hrun. injection Hrun as <-. replace (r+0) with r by lia. exact Hblank.
  - cbn [stepn step] in Hrun.
    destruct (tm q (t_head tp)) as [[w d p]|] eqn:Et; [|discriminate].
    pose proof (blank_radius_move tp r d w Hblank) as Hb.
    pose proof (IH (p,tape_move d w tp) c' (S r) Hb Hrun) as H.
    replace (r+S n) with (S r+n) by lia. exact H.
Qed.

Lemma blank_radius_from_blank : forall tm B cB,
  stepn tm B InitES = Some cB -> blank_radius (snd cB) B.
Proof.
  intros tm B cB Hrun.
  apply (blank_radius_run tm B InitES cB 0); [|exact Hrun].
  intros k _. split; reflexivity.
Qed.

Definition ahead (d : Dir) (tp : Tape) (n : nat) : Sym :=
  match n with
  | 0 => t_head tp
  | S k => match d with DL => t_left tp k | DR => t_right tp k end
  end.

Lemma ahead_move : forall d tp w n,
  ahead d (tape_move d w tp) n = ahead d tp (S n).
Proof. intros d tp w n. destruct d, n; reflexivity. Qed.

(** A scan may overwrite each visited cell arbitrarily. The bound uses the
    untouched cell ahead, so it covers both erasing and non-erasing sweeps. *)
Theorem sweep_reaches : forall tm p q d w1 w0 d0,
  tm p S1 = Some (mkTrans w1 d p) ->
  tm p S0 = Some (mkTrans w0 d0 q) ->
  forall n tp, ahead d tp n = S0 ->
  exists j cq, j <= S n /\ stepn tm j (p,tp) = Some cq /\ fst cq = q.
Proof.
  intros tm p q d w1 w0 d0 H1 H0 n.
  induction n as [|n IH]; intros tp Ha.
  - cbn [ahead] in Ha.
    exists 1, (q,tape_move d0 w0 tp). split; [lia|].
    split; [cbn [stepn step]; rewrite Ha,H0; reflexivity|reflexivity].
  - destruct (t_head tp) eqn:Eh.
    + exists 1, (q,tape_move d0 w0 tp). split; [lia|].
      split; [cbn [stepn step]; rewrite Eh,H0; reflexivity|reflexivity].
    + assert (Ha' : ahead d (tape_move d w1 tp) n = S0).
      { rewrite ahead_move. exact Ha. }
      destruct (IH _ Ha') as (j & cq & Hj & Hrun & Hq).
      exists (S j), cq. split; [lia|]. split; [|exact Hq].
      cbn [stepn step]. rewrite Eh,H1. exact Hrun.
Qed.

Corollary sweep_from_cutoff : forall tm p q d w1 w0 d0 B tp,
  tm p S1 = Some (mkTrans w1 d p) ->
  tm p S0 = Some (mkTrans w0 d0 q) ->
  stepn tm B InitES = Some (p,tp) ->
  BeepWindow tm q B (B+2).
Proof.
  intros tm p q d w1 w0 d0 B tp H1 H0 Hrun.
  pose proof (blank_radius_from_blank tm B (p,tp) Hrun B (Nat.le_refl B)) as [Hl Hr].
  assert (Ha : ahead d tp (S B) = S0) by (destruct d; assumption).
  destruct (sweep_reaches tm p q d w1 w0 d0 H1 H0 (S B) tp Ha)
    as (j & cq & Hj & Htail & Hq).
  exists (B+j). split; [lia|]. split; [lia|].
  exists cq. split; [rewrite stepn_add, Hrun; exact Htail|exact Hq].
Qed.

Print Assumptions sweep_from_cutoff.

Section TwoStateSweep.
Variable tm : TM.
Variable p q : St.
Variable dp dq ep eq : Dir.
Variable wp wq zp zq : Sym.
Hypothesis Hp1 : tm p S1 = Some (mkTrans wp dp p).
Hypothesis Hp0 : tm p S0 = Some (mkTrans zp ep q).
Hypothesis Hq1 : tm q S1 = Some (mkTrans wq dq q).
Hypothesis Hq0 : tm q S0 = Some (mkTrans zq eq p).

Lemma sweep_pair_step : forall c,
  fst c = p \/ fst c = q ->
  exists c', step tm c = Some c' /\ (fst c' = p \/ fst c' = q).
Proof.
  intros [s tp] [Hs|Hs]; cbn in Hs; subst s;
    destruct (t_head tp) eqn:Eh; cbn [step]; rewrite Eh;
    first [rewrite Hp0 | rewrite Hp1 | rewrite Hq0 | rewrite Hq1];
    eexists; split; try reflexivity; cbn; auto.
Qed.

Lemma sweep_pair_run : forall n c,
  fst c = p \/ fst c = q ->
  exists c', stepn tm n c = Some c' /\ (fst c' = p \/ fst c' = q).
Proof.
  induction n as [|n IH]; intros c Hc.
  - exists c; split; auto.
  - destruct (sweep_pair_step c Hc) as (c1 & Hstep & Hc1).
    destruct (IH c1 Hc1) as (c' & Hrun & Hc').
    exists c'. split; [cbn [stepn]; rewrite Hstep; exact Hrun|exact Hc'].
Qed.

Variable anchor : nat.
Variable ca : ExecState.
Hypothesis Hanchor : stepn tm anchor InitES = Some ca.
Hypothesis Hca : fst ca = p \/ fst ca = q.

Lemma sweep_pair_at : forall B, anchor <= B ->
  exists c, stepn tm B InitES = Some c /\ (fst c = p \/ fst c = q).
Proof.
  intros B HB. destruct (sweep_pair_run (B-anchor) ca Hca) as (c & Hr & Hc).
  exists c. split; [|exact Hc].
  replace B with (anchor+(B-anchor)) by lia. rewrite stepn_add,Hanchor. exact Hr.
Qed.

Theorem sweep_pair_nonhalt : NonHalt tm.
Proof.
  intros n Hnone. destruct (le_dec anchor n) as [Hle|Hle].
  - destruct (sweep_pair_at n Hle) as (c & Hr & _). congruence.
  - destruct (stepn_prefix tm n anchor InitES ca ltac:(lia) Hanchor)
      as (c & Hr & _). congruence.
Qed.

Theorem sweep_pair_window : forall B, anchor <= B -> WindowBound tm B (B+2).
Proof.
  intros B HB r (t & Ht & ct & Hrun & Hr).
  destruct (sweep_pair_at t ltac:(lia)) as (ct' & Hrun' & Hct).
  rewrite Hrun in Hrun'. injection Hrun' as <-.
  destruct (sweep_pair_at B HB) as ([s tp] & HBRun & Hs).
  cbn in Hs. destruct Hct as [Hp|Hq]; [assert (Er : r=p) by congruence|assert (Er : r=q) by congruence]; rewrite Er.
  - destruct Hs as [Hs|Hs]; subst s.
    + exists B. split; [lia|]. split; [lia|]. exists (p,tp). auto.
    + exact (sweep_from_cutoff tm q p dq wq zq eq B tp Hq1 Hq0 HBRun).
  - destruct Hs as [Hs|Hs]; subst s.
    + exact (sweep_from_cutoff tm p q dp wp zp ep B tp Hp1 Hp0 HBRun).
    + exists B. split; [lia|]. split; [lia|]. exists (q,tp). auto.
Qed.
End TwoStateSweep.

Print Assumptions sweep_pair_window.
Print Assumptions sweep_pair_nonhalt.

Definition sweep_tail_check (tm : TM) (anchor : nat) (p q : St) : bool :=
  match tm p S1, tm p S0, tm q S1, tm q S0, csteps tm anchor c0 with
  | Some p1, Some p0, Some q1, Some q0, Some ca =>
      st_eqb (t_next p1) p && st_eqb (t_next p0) q &&
      st_eqb (t_next q1) q && st_eqb (t_next q0) p &&
      (st_eqb (fst ca) p || st_eqb (fst ca) q)
  | _, _, _, _, _ => false
  end.

Theorem sweep_tail_check_sound : forall tm anchor p q,
  sweep_tail_check tm anchor p q = true ->
  NonHalt tm /\ forall B, anchor <= B -> WindowBound tm B (B+2).
Proof.
  intros tm anchor p q H. unfold sweep_tail_check in H.
  destruct (tm p S1) as [[wp dp p1]|] eqn:Hp1; [|discriminate].
  destruct (tm p S0) as [[zp ep p0]|] eqn:Hp0; [|discriminate].
  destruct (tm q S1) as [[wq dq q1]|] eqn:Hq1; [|discriminate].
  destruct (tm q S0) as [[zq eq q0]|] eqn:Hq0; [|discriminate].
  destruct (csteps tm anchor c0) as [ca|] eqn:Hanchor; [|discriminate].
  repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H0] H3] H2] Hca].
  apply st_eqb_spec in H1,H0,H3,H2. cbn in H1,H0,H3,H2. subst p1 p0 q1 q0.
  apply orb_true_iff in Hca. destruct Hca as [Hca|Hca]; apply st_eqb_spec in Hca;
    assert (Ha : stepn tm anchor InitES = Some (lift ca)) by
      (rewrite <- lift_c0; apply csteps_lift; exact Hanchor);
    assert (Hs : fst (lift ca) = p \/ fst (lift ca) = q) by (rewrite lift_state; auto);
    split.
  - exact (sweep_pair_nonhalt tm p q dp dq ep eq wp wq zp zq Hp1 Hp0 Hq1 Hq0 anchor (lift ca) Ha Hs).
  - exact (sweep_pair_window tm p q dp dq ep eq wp wq zp zq Hp1 Hp0 Hq1 Hq0 anchor (lift ca) Ha Hs).
  - exact (sweep_pair_nonhalt tm p q dp dq ep eq wp wq zp zq Hp1 Hp0 Hq1 Hq0 anchor (lift ca) Ha Hs).
  - exact (sweep_pair_window tm p q dp dq ep eq wp wq zp zq Hp1 Hp0 Hq1 Hq0 anchor (lift ca) Ha Hs).
Qed.

Theorem sweep_tail_check_completion : forall tm anchor p q,
  sweep_tail_check tm anchor p q = true ->
  forall tm', TM_le tm tm' -> NonHalt tm' /\
  forall B, anchor <= B -> WindowBound tm' B (B+2).
Proof.
  intros tm anchor p q H tm' Hle.
  destruct (sweep_tail_check_sound tm anchor p q H) as [HN HW].
  split; [eapply nonhalt_le; eauto|].
  intros B HB. apply (proj2 (window_bound_completion tm tm' B (B+2) HN Hle)).
  exact (HW B HB).
Qed.

Print Assumptions sweep_tail_check_completion.

Module SweepRegression.
Import List.ListNotations.
Definition expanding : TM := row_to_tm [t0RB;tN;t0LC;tN;t0LD;t1RC;t1RC;t1LD].
Example accepts_preserving_sweep : sweep_tail_check expanding 2 StC StD = true.
Proof. reflexivity. Qed.
Example rejects_unreached_pair : sweep_tail_check expanding 0 StC StD = false.
Proof. reflexivity. Qed.
Example rejects_missing_slot : sweep_tail_check expanding 2 StA StD = false.
Proof. reflexivity. Qed.
Definition escapes_pair : TM := row_to_tm [t0RB;tN;t0LC;tN;t0LA;t1RC;t1RC;t1LD].
Example rejects_nonclosing_pair : sweep_tail_check escapes_pair 2 StC StD = false.
Proof. reflexivity. Qed.
Definition halted_prefix : TM := row_to_tm [tN;tN;t0LC;tN;t0LD;t1RC;t1RC;t1LD].
Example rejects_halted_anchor : sweep_tail_check halted_prefix 2 StC StD = false.
Proof. reflexivity. Qed.
End SweepRegression.
