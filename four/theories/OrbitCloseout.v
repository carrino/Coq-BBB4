(** Close out completions of a proved board under symbol permutations and
    reflection, without enumerating every image as a separate proof. The
    start state and blank symbol stay fixed; state swapping is not an orbit
    operation and needs a separately checked prefix bridge. *)
From Coq Require Import List Bool NArith FunctionalExtensionality.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  Mirror CycleCensus Symmetry FamilyTransport StateOnlyCloseout.
Import ListNotations.

Definition orbit_check board tm :=
  existsb (fun p => existsb (fun mirrored =>
    board_check board (image_tm p mirrored tm)) [false; true]) all_SymPerm.
Definition orbit_remaining pending board tm := pending tm /\ orbit_check board tm = false.

Lemma image_bounds_back : forall bs bi p mirrored tm,
  Bounds bs bi (image_tm p mirrored tm) -> Bounds bs bi tm.
Proof.
  intros bs bi p mirrored tm H. unfold image_tm in H.
  destruct mirrored; [apply mirror_bounds in H|]; apply perm_bounds in H; exact H.
Qed.
Lemma image_state_bound_back : forall B p mirrored tm,
  QHBound B (image_tm p mirrored tm) -> QHBound B tm.
Proof.
  intros B p mirrored tm H. unfold image_tm in H.
  assert (Hperm : QHBound B (perm_tm p tm)).
  { destruct mirrored; [|exact H]. intros q n [Hv Hquiet]. apply (H q n).
    split; [apply mirror_visits; exact Hv|].
    intros k Hk Hvisit. apply (Hquiet k Hk). apply mirror_visits; exact Hvisit. }
  intros q n Hquiet. apply (Hperm q n). apply perm_quiet; exact Hquiet.
Qed.

Theorem orbit_check_sound : forall bs bi board tm,
  BoardSound bs bi board -> orbit_check board tm = true -> Bounds bs bi tm.
Proof.
  intros bs bi board tm Hboard H. unfold orbit_check in H.
  apply existsb_exists in H as (p & _ & H).
  apply existsb_exists in H as (mirrored & _ & H).
  apply board_check_sound with (bs:=bs) (bi:=bi) in H; [|exact Hboard].
  eapply image_bounds_back; exact H.
Qed.
Theorem orbit_check_state_sound : forall B board tm,
  StateBoardSound B board -> orbit_check board tm = true -> QHBound B tm.
Proof.
  intros B board tm Hboard H. unfold orbit_check in H.
  apply existsb_exists in H as (p & _ & H).
  apply existsb_exists in H as (mirrored & _ & H).
  apply state_board_check_sound with (B:=B) in H; [|exact Hboard].
  eapply image_state_bound_back; exact H.
Qed.

Theorem orbit_closeout_coverage : forall bs bi pending board,
  (forall tm, Bounds bs bi tm \/ pending tm) -> BoardSound bs bi board ->
  forall tm, Bounds bs bi tm \/ orbit_remaining pending board tm.
Proof.
  intros bs bi pending board Hcoverage Hsound tm.
  destruct (orbit_check board tm) eqn:E.
  - left. eapply orbit_check_sound; eauto.
  - destruct (Hcoverage tm); [left|right]; auto. split; assumption.
Qed.
Theorem orbit_state_coverage : forall B pending board,
  (forall tm, QHBound B tm \/ pending tm) -> StateBoardSound B board ->
  forall tm, QHBound B tm \/ orbit_remaining pending board tm.
Proof.
  intros B pending board Hcoverage Hsound tm.
  destruct (orbit_check board tm) eqn:E.
  - left. eapply orbit_check_state_sound; eauto.
  - destruct (Hcoverage tm); [left|right]; auto. split; assumption.
Qed.

Lemma perm_tm_identity : forall tm, perm_tm P123 tm = tm.
Proof.
  intro tm. apply functional_extensionality; intro q.
  apply functional_extensionality; intro s. unfold perm_tm.
  destruct s; cbn [perm_sym inverse_perm]; destruct (tm q _ ) as [[w d q']|];
    try reflexivity; destruct w; reflexivity.
Qed.
Lemma orbit_includes_direct : forall board tm,
  board_check board tm = true -> orbit_check board tm = true.
Proof.
  intros board tm H. apply existsb_exists. exists P123. split; [apply all_SymPerm_complete|].
  apply existsb_exists. exists false. split; [now left|].
  unfold image_tm. rewrite perm_tm_identity. exact H.
Qed.
Theorem orbit_remaining_subset : forall pending board tm,
  orbit_remaining pending board tm -> remaining pending board tm.
Proof.
  intros pending board tm [Hp Hmiss]. split; [exact Hp|].
  destruct (board_check board tm) eqn:E; [|reflexivity].
  apply orbit_includes_direct in E. congruence.
Qed.

Print Assumptions orbit_closeout_coverage.
Print Assumptions orbit_state_coverage.
