From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import PhaseRank.
From BBBWait42.PhaseRankReplay Require Import Base.
Import ListNotations.
From BBBWait42.PhaseRankReplay Require Import ExtraPart000 ExtraPart001 ExtraPart002 ExtraPart003 ExtraPart004.
Definition batches : list (list annotated_case) := [ExtraPart000.cases; ExtraPart001.cases; ExtraPart002.cases; ExtraPart003.cases; ExtraPart004.cases].
Definition cases := concat batches.
Lemma all_batches_checked : Forall (fun entries => checked entries = true) batches.
Proof. unfold batches.
 constructor; [exact ExtraPart000.all_checked|].
 constructor; [exact ExtraPart001.all_checked|].
 constructor; [exact ExtraPart002.all_checked|].
 constructor; [exact ExtraPart003.all_checked|].
 constructor; [exact ExtraPart004.all_checked|].
 constructor. Qed.
Example exact_case_count : length cases = 1263.
Proof. reflexivity. Qed.
Theorem all_completions : forall e, In e cases -> forall tm,
 TM_le (phase_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat width).
Proof.
 intros e Hin tm Hle. apply in_concat in Hin.
 destruct Hin as [entries [Hentries Hin]].
 pose proof all_batches_checked as HC; rewrite Forall_forall in HC.
 exact (cases_sound entries (HC entries Hentries) e Hin tm Hle).
Qed.
Print Assumptions all_completions.
