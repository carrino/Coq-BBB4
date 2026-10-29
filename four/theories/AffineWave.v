(** Batch reflection for affine certificates. Search results carry no proof:
    the Boolean checker and frozen-census membership are evaluated in Coq. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout IRuleCensus.
From BBB24.Checkers.IRules Require Import MetaBlkPfx.
Import ListNotations.

Definition AffineRows := list (TM * BIRCertP).
Definition affine_rows_check bs bi cfuel fuel (rows:AffineRows) :=
  forallb (fun row => ir_check bs bi (fst row) (snd row) cfuel fuel) rows.
Definition affine_rows_board (rows:AffineRows) := map fst rows.

Theorem affine_rows_sound : forall bs bi cfuel fuel rows,
  affine_rows_check bs bi cfuel fuel rows = true -> forall row,
  In row rows -> NonHalt (fst row) /\ Bounds bs bi (fst row).
Proof.
  intros bs bi cfuel fuel rows H row Hin.
  unfold affine_rows_check in H.
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply ir_check_sound; exact H.
Qed.
Theorem affine_rows_board_nonhalt : forall bs bi cfuel fuel rows,
  affine_rows_check bs bi cfuel fuel rows = true -> forall family,
  In family (affine_rows_board rows) -> NonHalt family.
Proof.
  intros bs bi cfuel fuel rows H family Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  exact (proj1 (affine_rows_sound _ _ _ _ _ H row Hin)).
Qed.
Theorem affine_rows_board_sound : forall bs bi cfuel fuel rows,
  affine_rows_check bs bi cfuel fuel rows = true ->
  BoardSound bs bi (affine_rows_board rows).
Proof.
  intros bs bi cfuel fuel rows H family Hin tm Hle.
  apply in_map_iff in Hin as (row & <- & Hin).
  destruct (affine_rows_sound _ _ _ _ _ H row Hin) as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.
Theorem affine_pending_sound : forall board,
  forallb (pending_check 9 empty bootstrap) board = true ->
  forall family, In family board -> bootstrap_pending family.
Proof.
  intros board H family Hin. apply pending_check_sound.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.

Lemma affine_concat_sound : forall bs bi boards,
  Forall (BoardSound bs bi) boards -> BoardSound bs bi (concat boards).
Proof.
  intros bs bi boards H. induction H; simpl.
  - intros family Hin. contradiction.
  - apply board_sound_app; assumption.
Qed.
Lemma affine_concat_all : forall (P:TM->Prop) boards,
  Forall (fun b => forall family, In family b -> P family) boards ->
  forall family, In family (concat boards) -> P family.
Proof.
  intros P boards H. induction H; intros family Hin; simpl in Hin.
  - contradiction.
  - apply in_app_iff in Hin as [Hin|Hin]; auto.
Qed.
Lemma affine_concat_checks : forall (P:TM->bool) boards,
  Forall (fun b => forallb P b = true) boards -> forallb P (concat boards) = true.
Proof.
  intros P boards H. induction H; [reflexivity|].
  cbn [concat]. rewrite forallb_app, H, IHForall. reflexivity.
Qed.

Print Assumptions affine_rows_board_sound.
