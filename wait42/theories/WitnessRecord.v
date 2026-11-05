(** Larger state waiting witness discovered by the finite exploratory scan.
    The certificate below independently checks every concrete step. *)
From Coq Require Import Arith Lia NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec.
From BBBWait42 Require Import Spec BinaryScan Witness.

(** 1RB1RC_1LA0LA_0RD0RC_1LD1LA *)
Definition record_wait_machine : TM := fun q a => Some
  (match q,a with
   | StA,S0 => mkTrans S1 DR StB | StA,S1 => mkTrans S1 DR StC
   | StB,S0 => mkTrans S1 DL StA | StB,S1 => mkTrans S0 DL StA
   | StC,S0 => mkTrans S0 DR StD | StC,S1 => mkTrans S0 DR StC
   | StD,S0 => mkTrans S1 DL StD | StD,S1 => mkTrans S1 DL StA
   end).
Definition record_wait : N := 225592668%N.
Definition record_horizon : N := (wait_start + record_wait)%N.

Theorem record_wait_check :
  first_hitN record_wait_machine (state_hit StB) wait_start record_wait = true.
Proof. vm_compute. reflexivity. Qed.

Theorem record_wait_lower_bound : forall w,
  WaitBound champion_score w -> N.to_nat record_wait <= w.
Proof.
  intros w H. change (WaitBound (N.to_nat wait_start) w) in H.
  exact (first_state_hitN_lower record_wait_machine StB wait_start record_wait record_wait_check w H).
Qed.

Theorem record_horizon_value : record_horizon = 258372146%N.
Proof. reflexivity. Qed.

Theorem record_horizon_lower_bound : forall w,
  WaitBound champion_score w -> N.to_nat record_horizon <= champion_score + w.
Proof.
  intros w H. unfold record_horizon. rewrite N2Nat.inj_add.
  change (N.to_nat wait_start + N.to_nat record_wait <= N.to_nat wait_start + w).
  apply Nat.add_le_mono_l. apply record_wait_lower_bound; exact H.
Qed.

Theorem record_wait_value_lower_bound : forall w,
  BBBWait42_is w -> N.to_nat record_wait <= w.
Proof. intros w [_ [H _]]. apply record_wait_lower_bound; exact H. Qed.

Theorem record_decision_value_lower_bound : forall D,
  BBBQHDecide42_is D -> N.to_nat record_horizon <= D.
Proof.
  intros D (w&[_ [H _]]&HD). subst D.
  apply record_horizon_lower_bound; exact H.
Qed.
