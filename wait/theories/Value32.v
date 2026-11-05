(** Exact state and instruction waiting values for three-state binary
    machines. All first transitions and every completion are covered. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement Size.
Require Import SmallBB.Value32.
From BBBWait Require Import Spec SpecTr Census Check32 Witness32.
From BBBWait.Census32 Require Import
  Shard00 Shard01 Shard02 Shard03 Shard04 Shard05 Shard06 Shard07 Shard08 Shard09 Shard10 Shard11 Shard12.
Import ListNotations.

Lemma all_state32_checked : check32_all state32_check = true.
Proof.
  unfold check32_all; apply forallb_forall; intros a Ha.
  unfold choices32 in Ha; cbn in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]].
  - subst a; exact state32_shard00.
  - subst a; exact state32_shard01.
  - subst a; exact state32_shard02.
  - subst a; exact state32_shard03.
  - subst a; exact state32_shard04.
  - subst a; exact state32_shard05.
  - subst a; exact state32_shard06.
  - subst a; exact state32_shard07.
  - subst a; exact state32_shard08.
  - subst a; exact state32_shard09.
  - subst a; exact state32_shard10.
  - subst a; exact state32_shard11.
  - subst a; exact state32_shard12.
  - contradiction.
Qed.

Lemma all_instr32_checked : check32_all instr32_check = true.
Proof.
  unfold check32_all; apply forallb_forall; intros a Ha.
  unfold choices32 in Ha; cbn in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]].
  - subst a; exact instr32_shard00.
  - subst a; exact instr32_shard01.
  - subst a; exact instr32_shard02.
  - subst a; exact instr32_shard03.
  - subst a; exact instr32_shard04.
  - subst a; exact instr32_shard05.
  - subst a; exact instr32_shard06.
  - subst a; exact instr32_shard07.
  - subst a; exact instr32_shard08.
  - subst a; exact instr32_shard09.
  - subst a; exact instr32_shard10.
  - subst a; exact instr32_shard11.
  - subst a; exact instr32_shard12.
  - contradiction.
Qed.

Theorem wait32_upper : WaitBound 3 2 55 38.
Proof.
  unfold WaitBound.
  exact (census32_sound _ state32_check state32_check_sound all_state32_checked).
Qed.

Theorem wait32_tr_upper : WaitBoundTr 3 2 55 173.
Proof.
  unfold WaitBoundTr.
  exact (census32_sound _ instr32_check instr32_check_sound all_instr32_checked).
Qed.

Theorem BBB_wait32_value : BBBWait_is 3 2 55 38.
Proof.
  split; [exact (proj1 SmallBB.Value32.BBB32_value)|].
  split; [exact wait32_upper|exact wait32_state_minimal].
Qed.

Theorem BBB_wait_tr32_value : BBBWaitTr_is 3 2 55 173.
Proof.
  split; [exact (proj2 SmallBB.Value32.BBB32_value)|].
  split; [exact wait32_tr_upper|exact wait32_instr_minimal].
Qed.

Print Assumptions BBB_wait32_value.
Print Assumptions BBB_wait_tr32_value.
