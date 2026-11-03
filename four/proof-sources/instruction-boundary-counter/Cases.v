(** Five exact original census tables enter the same B2-free counter. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24BoundaryNeighbors Require Import BoundaryKernel.
Import ListNotations.
Definition case_0 := bc_tm(Some(mkTrans S0 DR StB)).
Definition case_1 := bc_tm(Some(mkTrans S1 DL StA)).
Definition case_2 := bc_tm(Some(mkTrans S1 DL StB)).
Definition case_3 := bc_tm(Some(mkTrans S3 DL StA)).
Definition case_4 := bc_tm(Some(mkTrans S3 DR StA)).
Example entry_0:csteps case_0 40 c0=Some(main 1).
Proof. vm_compute;reflexivity. Qed.
Example entry_1:csteps case_1 44 c0=Some(main 1).
Proof. vm_compute;reflexivity. Qed.
Example entry_2:csteps case_2 36 c0=Some(main 1).
Proof. vm_compute;reflexivity. Qed.
Example entry_3:csteps case_3 19 c0=Some(main 0).
Proof. vm_compute;reflexivity. Qed.
Example entry_4:csteps case_4 64 c0=Some(main 1).
Proof. vm_compute;reflexivity. Qed.
Definition board:list TM:=[case_0;case_1;case_2;case_3;case_4].
Lemma board_entries:forall family,In family board->exists b2 p m,
 family=bc_tm b2 /\ p<=64 /\ csteps(bc_tm b2)p c0=Some(main m).
Proof.
 intros family Hin;cbn[board]in Hin;destruct Hin as[<-|[<-|[<-|[<-|[<-|Hbad]]]]];try contradiction.
 - exists(Some(mkTrans S0 DR StB)),40,1;repeat split;try lia;exact entry_0.
 - exists(Some(mkTrans S1 DL StA)),44,1;repeat split;try lia;exact entry_1.
 - exists(Some(mkTrans S1 DL StB)),36,1;repeat split;try lia;exact entry_2.
 - exists(Some(mkTrans S3 DL StA)),19,0;repeat split;try lia;exact entry_3.
 - exists(Some(mkTrans S3 DR StA)),64,1;repeat split;try lia;exact entry_4.
Qed.
Lemma nonhalt:forall family,In family board->NonHalt family.
Proof.
 intros family Hin;destruct(board_entries family Hin)as(b2&p&m&->&Hp&E).
 exact(entry_nonhalt b2 p m E).
Qed.
Lemma family_small:forall family,In family board->Bounds 0%N 64%N family.
Proof.
 intros family Hin;destruct(board_entries family Hin)as(b2&p&m&->&Hp&E).
 unfold Bounds;split.
 - exact(entry_state_zero b2 p m E).
 - intros tg s Hquiet;pose proof(entry_instruction_bound b2 p m E tg s Hquiet);cbn;lia.
Qed.
Lemma small_sound:BoardSound 0%N 64%N board.
Proof.
 intros family Hin tm Hle;eapply extend_bounds;[exact(nonhalt family Hin)|exact(family_small family Hin)|exact Hle].
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros family Hin tm Hle;eapply(bounds_weaken 0%N 64%N scoreN scoreN tm).
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
Print Assumptions sound.
