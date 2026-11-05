(** Exact state and instruction waiting values for two-state ternary
    machines. All first transitions and every completion are covered. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement Size.
Require Import SmallBB.Value23.
From BBBWait Require Import Spec SpecTr Census23 Check23 Witness23.
From BBBWait.Census23 Require Import
  Shard00 Shard01 Shard02 Shard03 Shard04 Shard05 Shard06 Shard07 Shard08 Shard09 Shard10 Shard11 Shard12.
Import ListNotations.

Lemma all_state23_checked : check23_all state23_check = true.
Proof.
  unfold check23_all; apply forallb_forall; intros a Ha.
  unfold choices23 in Ha; cbn in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]].
  - subst a; exact state23_shard00.
  - subst a; exact state23_shard01.
  - subst a; exact state23_shard02.
  - subst a; exact state23_shard03.
  - subst a; exact state23_shard04.
  - subst a; exact state23_shard05.
  - subst a; exact state23_shard06.
  - subst a; exact state23_shard07.
  - subst a; exact state23_shard08.
  - subst a; exact state23_shard09.
  - subst a; exact state23_shard10.
  - subst a; exact state23_shard11.
  - subst a; exact state23_shard12.
  - contradiction.
Qed.

Lemma all_instr23_checked : check23_all instr23_check = true.
Proof.
  unfold check23_all; apply forallb_forall; intros a Ha.
  unfold choices23 in Ha; cbn in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]].
  - subst a; exact instr23_shard00.
  - subst a; exact instr23_shard01.
  - subst a; exact instr23_shard02.
  - subst a; exact instr23_shard03.
  - subst a; exact instr23_shard04.
  - subst a; exact instr23_shard05.
  - subst a; exact instr23_shard06.
  - subst a; exact instr23_shard07.
  - subst a; exact instr23_shard08.
  - subst a; exact instr23_shard09.
  - subst a; exact instr23_shard10.
  - subst a; exact instr23_shard11.
  - subst a; exact instr23_shard12.
  - contradiction.
Qed.

Theorem wait23_upper : WaitBound 2 3 59 32.
Proof.
  unfold WaitBound.
  exact (census23_sound _ state23_check state23_check_sound all_state23_checked).
Qed.

Theorem wait23_tr_upper : WaitBoundTr 2 3 67 693.
Proof.
  unfold WaitBoundTr.
  exact (census23_sound _ instr23_check instr23_check_sound all_instr23_checked).
Qed.

Theorem BBB_wait23_value : BBBWait_is 2 3 59 32.
Proof.
  split; [exact (proj1 SmallBB.Value23.BBB23_value)|].
  split; [exact wait23_upper|exact wait23_state_minimal].
Qed.

Theorem BBB_wait_tr23_value : BBBWaitTr_is 2 3 67 693.
Proof.
  split; [exact (proj2 SmallBB.Value23.BBB23_value)|].
  split; [exact wait23_tr_upper|exact wait23_instr_minimal].
Qed.

Print Assumptions BBB_wait23_value.
Print Assumptions BBB_wait_tr23_value.
