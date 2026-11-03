(** One exact original census family, with every completion covered. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge Trace Final.
From BBB24InstructionS030 Require Import InstructionTail.
Import ListNotations.
Definition s30_board_boundN:N:=2199023255552%N.
Definition board:list TM:=[s30_tm].
Lemma s30_both_small : Bounds s30_board_boundN s30_board_boundN s30_tm.
Proof.
 unfold s30_board_boundN,Bounds;rewrite <-sf_bound_count;split.
 - exact(proj2 sf_sound).
 - intros tg s H;pose proof(s30_instruction_bound tg s H)as Hb.
   eapply Nat.le_trans;[exact Hb|apply sf_count_le;vm_compute;discriminate].
Qed.
Lemma small_sound : BoardSound s30_board_boundN s30_board_boundN board.
Proof.
 intros family[<-|Hbad]tm Hle;[|contradiction].
 eapply extend_bounds;[exact s30_nonhalt|exact s30_both_small|exact Hle].
Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
 intros family Hin tm Hle;eapply(bounds_weaken s30_board_boundN s30_board_boundN scoreN scoreN).
 - unfold s30_board_boundN,scoreN;vm_compute;discriminate.
 - unfold s30_board_boundN,scoreN;vm_compute;discriminate.
 - exact(small_sound family Hin tm Hle).
Qed.
Lemma nonhalt : forall family,In family board->NonHalt family.
Proof. intros family[<-|Hbad];[exact s30_nonhalt|contradiction]. Qed.
Lemma pending_checked : forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending : forall family,In family board->bootstrap_pending family.
Proof.
 intros family Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=family)in H;assumption.
Qed.
Print Assumptions sound.
