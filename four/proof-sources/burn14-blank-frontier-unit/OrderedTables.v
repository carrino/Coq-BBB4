(** Exact ordered equality, linear in the two lists. *)
From Coq Require Import List Bool.
From BBB24 Require Import Statement BoardManifest.
Import ListNotations.

Fixpoint ordered_tables_same (left right : list TM) : bool :=
  match left, right with
  | [], [] => true
  | x::xs, y::ys => table_same x y && ordered_tables_same xs ys
  | _, _ => false
  end.

Lemma ordered_tables_same_sound : forall left right,
  ordered_tables_same left right = true -> left = right.
Proof.
  induction left as [|x xs IH]; intros [|y ys] H; simpl in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [Hxy Hrest].
    apply table_same_sound in Hxy. apply IH in Hrest. now subst.
Qed.

Print Assumptions ordered_tables_same_sound.
