From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import PhaseRank.
From BBBWait42.PhaseRankReplay Require Import Base.
Import ListNotations.
From BBBWait42.PhaseRankReplay Require Import All ExtraAll.
Definition cases : list annotated_case := All.cases ++ ExtraAll.cases.
Example exact_case_count : length cases = 7095.
Proof. reflexivity. Qed.
Theorem all_completions : forall e, In e cases -> forall tm,
 TM_le (phase_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat width).
Proof.
 intros e Hin tm Hle. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
 - exact (All.all_completions e Hin tm Hle).
 - exact (ExtraAll.all_completions e Hin tm Hle).
Qed.
Print Assumptions all_completions.
