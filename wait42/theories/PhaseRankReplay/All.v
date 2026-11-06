From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import PhaseRank.
From BBBWait42.PhaseRankReplay Require Import Base.
Import ListNotations.
From BBBWait42.PhaseRankReplay Require Import Part000 Part001 Part002 Part003 Part004 Part005 Part006 Part007 Part008 Part009 Part010 Part011 Part012 Part013 Part014 Part015 Part016 Part017 Part018 Part019 Part020 Part021 Part022.
Definition batches : list (list annotated_case) := [Part000.cases; Part001.cases; Part002.cases; Part003.cases; Part004.cases; Part005.cases; Part006.cases; Part007.cases; Part008.cases; Part009.cases; Part010.cases; Part011.cases; Part012.cases; Part013.cases; Part014.cases; Part015.cases; Part016.cases; Part017.cases; Part018.cases; Part019.cases; Part020.cases; Part021.cases; Part022.cases].
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
 constructor; [exact Part012.all_checked|].
 constructor; [exact Part013.all_checked|].
 constructor; [exact Part014.all_checked|].
 constructor; [exact Part015.all_checked|].
 constructor; [exact Part016.all_checked|].
 constructor; [exact Part017.all_checked|].
 constructor; [exact Part018.all_checked|].
 constructor; [exact Part019.all_checked|].
 constructor; [exact Part020.all_checked|].
 constructor; [exact Part021.all_checked|].
 constructor; [exact Part022.all_checked|].
 constructor. Qed.
Example exact_case_count : length cases = 5832.
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
