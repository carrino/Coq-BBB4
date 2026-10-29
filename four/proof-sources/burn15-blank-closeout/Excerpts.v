(** Ordered source excerpts use a single scan, with exact table equality. *)
From Coq Require Import List Bool.
From BBB24 Require Import Statement BoardManifest StateOnlyCloseout.
Import ListNotations.

Fixpoint excerpt_check (original selected : list TM) {struct original} : bool :=
  match selected with
  | [] => true
  | x::xs => match original with
    | [] => false
    | y::ys => if table_same x y then excerpt_check ys xs
               else excerpt_check ys selected
    end
  end.

Lemma excerpt_members : forall original selected,
  excerpt_check original selected = true ->
  forall family, In family selected -> In family original.
Proof.
  induction original as [|y ys IH]; intros [|x xs] H family Hin;
    simpl in H,Hin; try contradiction; try discriminate.
  destruct (table_same x y) eqn:E.
  - apply table_same_sound in E. subst x. destruct Hin as [<-|Hin].
    + now left.
    + right. exact (IH xs H family Hin).
  - right. exact (IH (x::xs) H family Hin).
Qed.

Theorem excerpt_state_sound : forall bound original selected,
  StateBoardSound bound original -> excerpt_check original selected = true ->
  StateBoardSound bound selected.
Proof.
  intros bound original selected Hsound H family Hin complete Hle.
  exact (Hsound family (excerpt_members original selected H family Hin) complete Hle).
Qed.

Print Assumptions excerpt_state_sound.
