(** The first four affine families attached to the frozen census.
    This refines its pending predicate; it does not claim that an entire
    eight-step leaf disappears or recompute the original structural weights. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout AffineExamples.
Import ListNotations.

Definition affine_board : list TM :=
  [tm_0LB0LAXXX2RB_3RA1LB1RB1LB;
   tm_0LB1LB2RA0RB_3RA3RB1LA2LB;
   tm_0LB2RA3RB2LA_1RA2RA3LB2RB;
   tm_0LB3RB0LA1RB_3RA3LB0LA2LB].

Lemma affine_board_small_sound : BoardSound 4096%N 4096%N affine_board.
Proof.
  intros family Hin tm Hle.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]].
  - apply completions_0LB0LAXXX2RB_3RA1LB1RB1LB; exact Hle.
  - apply completions_0LB1LB2RA0RB_3RA3RB1LA2LB; exact Hle.
  - apply completions_0LB2RA3RB2LA_1RA2RA3LB2RB; exact Hle.
  - apply completions_0LB3RB0LA1RB_3RA3LB0LA2LB; exact Hle.
Qed.
Lemma affine_board_sound : BoardSound scoreN scoreN affine_board.
Proof.
  intros family Hin tm Hle. eapply (bounds_weaken 4096%N 4096%N scoreN scoreN tm).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (affine_board_small_sound family Hin tm Hle).
Qed.

Definition bootstrap_affine_pending := remaining bootstrap_pending affine_board.
Theorem bootstrap_affine_coverage : forall tm,
  Bounds scoreN scoreN tm \/ bootstrap_affine_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage affine_board_sound). Qed.
Theorem bootstrap_upper_if_affine_remaining :
  (forall tm, bootstrap_affine_pending tm -> Bounds scoreN scoreN tm) ->
  forall tm, Bounds scoreN scoreN tm.
Proof.
  apply (closeout_upper_if_remaining _ _ _ _ bootstrap_coverage affine_board_sound).
Qed.

Lemma affine_board_pending_checked :
  forallb (pending_check 9 empty bootstrap) affine_board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma affine_board_was_pending : forall family, In family affine_board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound.
  pose proof affine_board_pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.

Lemma closeout_tm_le_trans : forall a b c, TM_le a b -> TM_le b c -> TM_le a c.
Proof.
  intros a b c Hab Hbc q s. destruct (Hab q s) as [H|H]; [left; exact H|].
  destruct (Hbc q s) as [H'|H']; [left|right]; congruence.
Qed.
Theorem affine_families_discharged : forall family,
  In family affine_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ Bounds scoreN scoreN tm /\ ~ bootstrap_affine_pending tm.
Proof.
  intros family Hin tm Hle. split.
  - destruct (affine_board_was_pending family Hin) as (leaf & Hleaf & Hlf).
    exists leaf. split; [exact Hleaf|]. eapply closeout_tm_le_trans; eauto.
  - split; [exact (affine_board_sound family Hin tm Hle)|].
    intros [_ Hremaining].
    assert (Hhit : board_check affine_board tm = true).
    { apply existsb_exists. exists family. split; [exact Hin|].
      apply table_leb_spec. exact Hle. }
    congruence.
Qed.

(** Negative checks exercise undefined entries and the bounded DAG descent. *)
Example empty_board_does_not_discharge : board_check [] champion = false.
Proof. reflexivity. Qed.
Example unlisted_champion_remains_unmatched : board_check affine_board champion = false.
Proof. vm_compute. reflexivity. Qed.
Example incomplete_depth_does_not_claim_pending :
  pending_check 0 empty bootstrap tm_0LB2RA3RB2LA_1RA2RA3LB2RB = false.
Proof. reflexivity. Qed.
Example invalid_node_does_not_claim_pending :
  pending_check 9 empty Invalid tm_0LB2RA3RB2LA_1RA2RA3LB2RB = false.
Proof. reflexivity. Qed.
Example contradictory_table_does_not_match :
  table_leb tm_0LB2RA3RB2LA_1RA2RA3LB2RB champion = false.
Proof. reflexivity. Qed.

Print Assumptions bootstrap_affine_coverage.
Print Assumptions affine_families_discharged.
