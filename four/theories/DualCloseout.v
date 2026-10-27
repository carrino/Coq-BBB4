(** Keep the state and instruction remainders separate. A state-only proof
    refines state coverage; it does not discharge an instruction obligation. *)
From Coq Require Import List Bool NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard StateOnlyCloseout.
Import ListNotations.

Lemma bounds_board_state : forall board,
  BoardSound scoreN scoreN board -> StateBoardSound score board.
Proof. intros board H family Hin tm Hle. exact (proj1 (H family Hin tm Hle)). Qed.

Lemma state_board_app : forall B left right,
  StateBoardSound B left -> StateBoardSound B right ->
  StateBoardSound B (left ++ right).
Proof.
  intros B left right Hl Hr family Hin tm Hle.
  apply in_app_iff in Hin as [Hin|Hin]; [eapply Hl|eapply Hr]; eauto.
Qed.

Lemma pending_board_app : forall left right,
  (forall family, In family left -> bootstrap_pending family) ->
  (forall family, In family right -> bootstrap_pending family) ->
  forall family, In family (left ++ right) -> bootstrap_pending family.
Proof. intros left right Hl Hr family Hin. apply in_app_iff in Hin as [H|H]; auto. Qed.

Section Closeout.
Variables both_board state_only_board : list TM.
Hypothesis both_sound : BoardSound scoreN scoreN both_board.
Hypothesis state_only_sound : StateBoardSound score state_only_board.
Hypothesis both_was_pending : forall family, In family both_board -> bootstrap_pending family.
Hypothesis state_only_was_pending : forall family, In family state_only_board -> bootstrap_pending family.

Definition dual_state_board := both_board ++ state_only_board.
Definition dual_both_pending := remaining bootstrap_pending both_board.
Definition dual_state_pending := remaining bootstrap_pending dual_state_board.

Theorem dual_both_coverage : forall tm,
  Bounds scoreN scoreN tm \/ dual_both_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage both_sound). Qed.

Lemma dual_state_sound : StateBoardSound score dual_state_board.
Proof. apply state_board_app; [apply bounds_board_state; exact both_sound|exact state_only_sound]. Qed.
Lemma dual_state_was_pending : forall family,
  In family dual_state_board -> bootstrap_pending family.
Proof. apply pending_board_app; assumption. Qed.

Theorem dual_state_coverage : forall tm,
  QHBound score tm \/ dual_state_pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage dual_state_sound). Qed.

Theorem dual_both_families_discharged : forall family,
  In family both_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ Bounds scoreN scoreN tm /\ ~ dual_both_pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ both_was_pending both_sound). Qed.

Theorem dual_state_families_discharged : forall family,
  In family dual_state_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ QHBound score tm /\ ~ dual_state_pending tm.
Proof. exact (state_board_discharge _ _ dual_state_was_pending dual_state_sound). Qed.

Theorem dual_state_pending_subset : forall tm,
  dual_state_pending tm -> dual_both_pending tm.
Proof.
  intros tm [Hp Hmiss]. split; [exact Hp|].
  unfold board_check, dual_state_board in Hmiss. rewrite existsb_app in Hmiss.
  apply orb_false_iff in Hmiss. exact (proj1 Hmiss).
Qed.
End Closeout.

Print Assumptions dual_state_coverage.
Print Assumptions dual_both_coverage.
