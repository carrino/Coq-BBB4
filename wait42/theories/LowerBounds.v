(** Public lower-bound statements for both total observation horizons. *)
From Coq Require Import Arith NArith.
From BBB4 Require Import BBB4_Spec.
From BBBWait42 Require Import Spec Witness Examples WitnessRecord.

Definition instruction_horizon : N := (wait_start + instruction_wait)%N.

Theorem instruction_horizon_value : instruction_horizon = 487181856%N.
Proof. reflexivity. Qed.

Theorem instruction_horizon_lower_bound : forall w,
  WaitBoundTr champion_score w ->
  N.to_nat instruction_horizon <= champion_score + w.
Proof.
  intros w H. unfold instruction_horizon. rewrite N2Nat.inj_add.
  change (N.to_nat wait_start + N.to_nat instruction_wait <= N.to_nat wait_start + w).
  apply Nat.add_le_mono_l. apply instruction_wait_lower_bound. exact H.
Qed.

Theorem instruction_decision_value_lower_bound : forall D,
  BBBQHDecideTr42_is D -> N.to_nat instruction_horizon <= D.
Proof.
  intros D (w & [_ [H _]] & HD). subst D.
  apply instruction_horizon_lower_bound; exact H.
Qed.

Print Assumptions record_decision_value_lower_bound.
Print Assumptions instruction_decision_value_lower_bound.
