(** Exact census registration of the universal eight-instruction recurrence proof. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24SparseReturn Require Import BoundaryCounter.
Import ListNotations.

Lemma exact_complete_table:forall q s,
 sp_tm q s=machine_of_codes[5;9;14;13;7;4;14;6]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Definition board:list TM:=[sp_tm].
Lemma nonhalt:forall family,In family board->NonHalt family.
Proof. intros family[<-|Hbad];[exact(proj1 family_zero)|contradiction]. Qed.
Lemma small_sound:BoardSound 0%N 0%N board.
Proof.
 intros family[<-|Hbad]tm Hle;[|contradiction].
 eapply extend_bounds;[exact(proj1 family_zero)|exact(proj2 family_zero)|exact Hle].
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros family Hin tm Hle;eapply(bounds_weaken 0%N 0%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound family Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall family,In family board->bootstrap_pending family.
Proof.
 intros family Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=family)in H;assumption.
Qed.
Print Assumptions small_sound.
