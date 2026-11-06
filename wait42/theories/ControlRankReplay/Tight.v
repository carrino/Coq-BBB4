From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import ControlRank.
From BBBWait42.ControlRankReplay Require Import Base All.
Import ListNotations.
Definition tight_width : N := 98338439%N.
Example all_checked_tight :
 control_rank_batch_check (map payload All.cases) cutoff tight_width = true.
Proof. native_compute. reflexivity. Qed.
Theorem all_completions : forall e, In e All.cases -> forall tm,
 TM_le (cr_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat tight_width).
Proof.
 intros e Hin tm Hle.
 apply (control_rank_batch_completion (map payload All.cases)
   cutoff tight_width all_checked_tight (payload e)).
 - now apply in_map.
 - exact Hle.
Qed.
Print Assumptions all_completions.
