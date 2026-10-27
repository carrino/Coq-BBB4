(** One exact state-only census family; no instruction-bound claim. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard CensusUnion StateOnlyCloseout BoardManifest.
From BBB24Burn3RelaxedMarker Require Import RelaxedMarker Regression.
Import ListNotations.
Definition rows : list N := [4967611060%N].
Definition board : list TM := [rmp_example].
Lemma inventory_checked : manifest_check rows board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem inventory_exact : manifest_board rows=board.
Proof. apply manifest_check_sound;exact inventory_checked. Qed.
Theorem small_sound : StateBoardSound 0 board.
Proof.
 intros family Hin tm Hle. destruct Hin as[<-|Hbad];[|contradiction].
 eapply state_bound_extend;
 [exact rmp_example_nonhalt|exact rmp_example_state_zero|exact Hle].
Qed.
Theorem sound : StateBoardSound score board.
Proof. apply state_board_zero_weaken;exact small_sound. Qed.
Lemma pending_checked : forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem was_pending : forall family,In family board -> bootstrap_pending family.
Proof.
 intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
 apply forallb_forall with(x:=family)in H;assumption.
Qed.
Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm,QHBound score tm \/ pending tm.
Proof. exact(state_closeout_coverage _ _ _ bootstrap_state_coverage sound). Qed.
Theorem discharged : forall family,In family board -> forall tm,TM_le family tm ->
 bootstrap_pending tm /\ QHBound score tm /\ ~pending tm.
Proof. exact(state_board_discharge _ _ was_pending sound). Qed.
Print Assumptions discharged.
