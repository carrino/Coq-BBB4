From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import PhaseRank.
Import ListNotations.
Record annotated_case := TaggedCase {
 source_index : N; diagnostic_source_index : N; union_source_index : N;
 pointer : nat; payload : phase_case }.
Definition cutoff : N := 32779478%N.
Definition width : N := 98338534%N.
Definition bool4 (a b c d : bool) : St -> bool := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition label4 (a b c d : nat) : St -> nat := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition nat3 (a b c : nat) (n : nat) := match n with 1 => a | 2 => b | 3 => c | _ => 0 end.
Definition bool3 (a b c : bool) (n : nat) := match n with 1 => a | 2 => b | 3 => c | _ => false end.
Definition dir3 (a b c : Dir) (n : nat) := match n with 1 => a | 2 => b | 3 => c | _ => DR end.
Definition rank (la lb lc ld c1 c2 c3 : nat) (k1 k2 k3 : bool) (d1 d2 d3 : Dir) :=
 mkPhaseRank (label4 la lb lc ld) (nat3 c1 c2 c3) (bool3 k1 k2 k3) (dir3 d1 d2 d3).
Definition rank4 (a b c d : phase_rank) : St -> phase_rank := fun q => match q with
 | StA => a | StB => b | StC => c | StD => d end.
Definition checked (entries : list annotated_case) :=
 control_phase_batch_check (map payload entries) cutoff width.
Theorem cases_sound : forall entries, checked entries = true ->
 forall e, In e entries -> forall tm, TM_le (phase_machine (payload e)) tm ->
 NonHalt tm /\ WindowBound tm (N.to_nat cutoff) (N.to_nat width).
Proof.
 intros entries H e Hin tm Hle. unfold checked in H.
 apply (control_phase_batch_completion (map payload entries) cutoff width H (payload e)).
 - now apply in_map.
 - exact Hle.
Qed.
