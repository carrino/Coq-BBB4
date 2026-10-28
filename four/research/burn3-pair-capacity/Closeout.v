From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout CertifiedBoard InstructionPortfolio.
From BBB24Burn3Pair Require Import GraphCertificate.
Import ListNotations.
Lemma all_instructions_recur:forall tg N,exists k,N<=k /\ FiresAt family tg k.
Proof.
 intros [q h] N;destruct q,h.
 all:try(apply(proj2 seven_sound);unfold targets;simpl;tauto).
 exact(proj2 eighth_sound N).
Qed.
Theorem exact_bounds:NonHalt family /\ Bounds 0%N 0%N family.
Proof. apply wp_all_recur_sound;exact all_instructions_recur. Qed.
Definition board:list TM:=[family].
Lemma small_sound:BoardSound 0%N 0%N board.
Proof.
 intros f[<-|Hfalse]tm Hle;[|contradiction].
 destruct exact_bounds as[Hnh Hb];eapply extend_bounds;eauto.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 0%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound f Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall f,In f board -> bootstrap_pending f.
Proof.
 intros f Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=f)in H;assumption.
Qed.
Print Assumptions exact_bounds.
