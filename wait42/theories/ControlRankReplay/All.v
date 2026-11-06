From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import ControlRank.
From BBBWait42.ControlRankReplay Require Import Base.
Import ListNotations.
From BBBWait42.ControlRankReplay Require Import Part000 Part001 Part002 Part003 Part004 Part005 Part006 Part007 Part008 Part009 Part010 Part011.
Definition batches : list (list annotated_case) := [Part000.cases; Part001.cases; Part002.cases; Part003.cases; Part004.cases; Part005.cases; Part006.cases; Part007.cases; Part008.cases; Part009.cases; Part010.cases; Part011.cases].
Definition cases := concat batches.
Lemma all_batches_checked : Forall (fun entries => checked entries = true) batches.
Proof. unfold batches.
 constructor; [exact Part000.all_checked|].
 constructor; [exact Part001.all_checked|].
 constructor; [exact Part002.all_checked|].
 constructor; [exact Part003.all_checked|].
 constructor; [exact Part004.all_checked|].
 constructor; [exact Part005.all_checked|].
 constructor; [exact Part006.all_checked|].
 constructor; [exact Part007.all_checked|].
 constructor; [exact Part008.all_checked|].
 constructor; [exact Part009.all_checked|].
 constructor; [exact Part010.all_checked|].
 constructor; [exact Part011.all_checked|].
 constructor. Qed.
Example exact_case_count : length cases = 2874.
Proof. reflexivity. Qed.
Theorem all_completions : forall e, In e cases -> forall tm,
 TM_le (cr_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat width).
Proof.
 intros e Hin tm Hle. apply in_concat in Hin.
 destruct Hin as [entries [Hentries Hin]].
 pose proof all_batches_checked as HC; rewrite Forall_forall in HC.
 exact (cases_sound entries (HC entries Hentries) e Hin tm Hle).
Qed.
Print Assumptions all_completions.
