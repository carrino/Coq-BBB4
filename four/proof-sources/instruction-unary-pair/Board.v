(** The shared proof registers two distinct exact census families. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24Burn23S004S005Unary Require Import UnaryPhases.
From BBB24InstructionUnaryPair Require Import UnaryInstructions.
Import ListNotations.

Example exact_table_false : forall q s,
 pu_tm false q s=machine_of_codes[5;0;5;7;15;14;3;8]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Example exact_table_true : forall q s,
 pu_tm true q s=machine_of_codes[5;0;5;7;15;14;11;8]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Definition board:list TM:=[pu_tm false;pu_tm true].
Lemma small_sound:BoardSound 0%N 0%N board.
Proof.
 intros family[<-|[<-|Hbad]]tm Hle;try contradiction;
 eapply extend_bounds;[apply(proj1(pu_both_zero false))|apply(proj2(pu_both_zero false))|exact Hle|
                      apply(proj1(pu_both_zero true))|apply(proj2(pu_both_zero true))|exact Hle].
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
