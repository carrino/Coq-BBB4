(** One exact census family with composed state recurrence; all completions. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout
  StateOnlyCloseout BoardManifest.
From BBB24Burn4MarkerComposition Require Import CompositionExample.
Import ListNotations.
Definition rows : list N := [45010956%N].
Definition board : list TM := [mh_example].
Lemma inventory_checked : manifest_check rows board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem inventory_exact : manifest_board rows=board.
Proof. apply manifest_check_sound;exact inventory_checked. Qed.
Theorem small_sound : StateBoardSound 0 board.
Proof.
 intros family Hin tm Hle. destruct Hin as[<-|Hbad];[|contradiction].
 eapply state_bound_extend;
 [exact mh_example_nonhalt|exact mh_example_state_zero|exact Hle].
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
Print Assumptions small_sound.
