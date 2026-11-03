From Coq Require Import List NArith Lia.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24ThreeCounter Require Import ThreeEntry ConjugateThree.
Import ListNotations.
Definition board:list TM:=[three_tm;conjugate_three_tm].
Lemma nonhalt:forall family,In family board->NonHalt family.
Proof.
 intros family[<-|[<-|Hbad]];
 [exact three_nonhalt|exact conjugate_three_nonhalt|contradiction].
Qed.
Lemma small_sound:BoardSound 0%N 2%N board.
Proof.
 intros family Hin tm Hle;destruct Hin as[<-|[<-|Hbad]];[| |contradiction].
 - eapply extend_bounds;[exact three_nonhalt|exact(proj2 three_family_run)|exact Hle].
 - assert(Hbound:Bounds 0%N 2%N conjugate_three_tm).
   { destruct(proj2 conjugate_three_family_run)as[Hs Hi];split;[exact Hs|].
     intros tg s Hlast;specialize(Hi tg s Hlast);cbn in Hi|-*;lia. }
   eapply extend_bounds;[exact conjugate_three_nonhalt|exact Hbound|exact Hle].
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
