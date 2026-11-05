From Coq Require Import List NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24CounterEntry Require Import CounterEntry.
Import ListNotations.
Definition board:list TM:=map rb_tm[S0;S1;S2;S3].
Lemma nonhalt:forall family,In family board->NonHalt family.
Proof.
 intros family Hin;apply in_map_iff in Hin;destruct Hin as(w&<-&_).
 apply rb_nonhalt.
Qed.
Lemma small_sound:BoardSound 0%N 2%N board.
Proof.
 intros family Hin tm Hle;apply in_map_iff in Hin;destruct Hin as(w&<-&_).
 eapply extend_bounds;[exact(rb_nonhalt w)|exact(proj2(rb_family_run w))|exact Hle].
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros family Hin tm Hle;eapply(bounds_weaken 0%N 2%N scoreN scoreN tm).
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
