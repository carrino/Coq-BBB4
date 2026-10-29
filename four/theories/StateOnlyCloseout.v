(** A state-only closeout is deliberately separate from the both-bound board.
    Removing an obligation here makes no instruction-bound claim. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement Spec CTape Bounds Census Bootstrap Closeout.
Import ListNotations.

Definition StateBoardSound B (board : list TM) :=
  forall family, In family board -> forall tm, TM_le family tm -> QHBound B tm.
Lemma state_bound_extend : forall B tm tm',
  NonHalt tm -> QHBound B tm -> TM_le tm tm' -> QHBound B tm'.
Proof.
  intros B tm tm' Hnh Hb Hle.
  assert (Hv : forall q n, VisitsAt tm' q n <-> VisitsAt tm q n).
  { intros q n. unfold VisitsAt. rewrite (extend_run tm tm' Hnh Hle n). tauto. }
  intros q s [Hq Hquiet]. apply (Hb q s). split; [apply Hv; exact Hq|].
  intros n Hn Hqn. apply (Hquiet n Hn). apply Hv; exact Hqn.
Qed.
Lemma state_board_zero_weaken : forall B board,
  StateBoardSound 0 board -> StateBoardSound B board.
Proof.
  intros B board H family Hin tm Hle q s Hquiet.
  pose proof (H family Hin tm Hle q s Hquiet). lia.
Qed.
Lemma state_boards_sound : forall B boards,
  Forall (StateBoardSound B) boards -> StateBoardSound B (concat boards).
Proof.
  intros B boards H family Hin tm Hle.
  apply in_concat in Hin as (board & Hb & Hin).
  apply Forall_forall with (x:=board) in H; [exact (H family Hin tm Hle)|exact Hb].
Qed.
Lemma state_board_check_sound : forall B board tm,
  StateBoardSound B board -> board_check board tm = true -> QHBound B tm.
Proof.
  intros B board tm Hsound H. apply existsb_exists in H as (family&Hin&Hle).
  apply table_leb_spec in Hle. exact (Hsound family Hin tm Hle).
Qed.
Theorem state_closeout_coverage : forall B pending board,
  (forall tm, QHBound B tm \/ pending tm) -> StateBoardSound B board ->
  forall tm, QHBound B tm \/ remaining pending board tm.
Proof.
  intros B pending board Hcoverage Hsound tm.
  destruct (board_check board tm) eqn:E.
  - left. eapply state_board_check_sound; eauto.
  - destruct (Hcoverage tm); [left|right]; auto. split; assumption.
Qed.
Theorem bootstrap_state_coverage : forall tm,
  QHBound score tm \/ bootstrap_pending tm.
Proof.
  intro tm. destruct (bootstrap_coverage tm) as [[Hs _]|Hp]; [left|right]; assumption.
Qed.
Theorem state_board_discharge : forall B board,
  (forall family, In family board -> bootstrap_pending family) -> StateBoardSound B board ->
  forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\ QHBound B tm /\ ~ remaining bootstrap_pending board tm.
Proof.
  intros B board Hp Hs family Hin tm Hle.
  split.
  - destruct (Hp family Hin) as (leaf&Hleaf&Hlf). exists leaf. split; [exact Hleaf|].
    intros q s. destruct (Hlf q s) as [H|H]; [left;exact H|].
    destruct (Hle q s) as [H'|H']; [left|right]; congruence.
  - split; [exact (Hs family Hin tm Hle)|]. intros [_ Hremaining].
    assert (Hhit : board_check board tm=true).
    { apply existsb_exists. exists family. split; [exact Hin|]. apply table_leb_spec; exact Hle. }
    congruence.
Qed.
