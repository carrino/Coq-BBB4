From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import ControlRank.
Import ListNotations.
Record annotated_case := TaggedCase {
 source_index : N; union_source_index : N; pointer : nat; payload : cr_case }.
Definition cutoff : N := 32779478%N.
Definition width : N := 225592668%N.
Definition bool4 (a b c d : bool) : St -> bool := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition phi4 (a b c d : nat) : St -> nat := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition rank (m : cr_measure) (scale a b c d : nat) := mkCRank m scale (phi4 a b c d).
Definition rank4 (a b c d : cr_rank) : St -> cr_rank := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition checked (entries : list annotated_case) :=
 control_rank_batch_check (map payload entries) cutoff width.
Theorem cases_sound : forall entries, checked entries = true ->
 forall e, In e entries -> forall tm, TM_le (cr_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat width).
Proof.
 intros entries H e Hin tm Hle. unfold checked in H.
 apply (control_rank_batch_completion (map payload entries) cutoff width H (payload e)).
 - now apply in_map.
 - exact Hle.
Qed.
