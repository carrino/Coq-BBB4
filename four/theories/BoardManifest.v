(** Check that a report's ordered machine inventory is exactly the board used
    by its theorem. This check adds no mathematical assumption to closeout. *)
From Coq Require Import List NArith Bool FunctionalExtensionality.
From BBB24 Require Import Statement Census Closeout Pipeline.
Import ListNotations.

Fixpoint manifest_codes fuel (packed : N) : list nat :=
  match fuel with
  | 0 => []
  | S f => N.to_nat (packed mod 17)%N :: manifest_codes f (packed / 17)%N
  end.
Definition manifest_machine packed := machine_of_codes (manifest_codes 8 packed).
Definition manifest_board rows := map manifest_machine rows.

Definition table_same left right := table_leb left right && table_leb right left.
Lemma table_same_sound : forall left right,
  table_same left right = true -> left = right.
Proof.
  intros left right H. apply andb_true_iff in H as [Hl Hr].
  apply table_leb_spec in Hl. apply table_leb_spec in Hr.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  specialize (Hl q s); specialize (Hr q s).
  destruct Hl as [Hl|Hl], Hr as [Hr|Hr]; congruence.
Qed.

Fixpoint manifest_check (rows : list N) (board : list TM) : bool :=
  match rows, board with
  | [], [] => true
  | packed :: tail, tm :: rest =>
      if table_same (manifest_machine packed) tm then manifest_check tail rest else false
  | _, _ => false
  end.
Theorem manifest_check_sound : forall rows board,
  manifest_check rows board = true -> manifest_board rows = board.
Proof.
  induction rows as [|packed tail IH]; intros [|tm rest] H; try discriminate.
  - reflexivity.
  - cbn [manifest_check] in H.
    destruct (table_same (manifest_machine packed) tm) eqn:E; [|discriminate].
    apply table_same_sound in E. apply IH in H.
    unfold manifest_board in *. simpl. now rewrite E, H.
Qed.

Example manifest_rejects_extra_row : manifest_check [0%N] [] = false.
Proof. reflexivity. Qed.
Example manifest_rejects_missing_row : manifest_check [] [manifest_machine 0%N] = false.
Proof. reflexivity. Qed.
Example manifest_rejects_changed_table :
  manifest_check [0%N] [manifest_machine 1%N] = false.
Proof. vm_compute. reflexivity. Qed.
Example manifest_keeps_partial_cells :
  manifest_check [16%N] [manifest_machine 0%N] = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions manifest_check_sound.
