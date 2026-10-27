(** A closed partial-table family can include halting machines. This regression
    exercises all sixteen defined choices and the separate None/halting case. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Pipeline CycleBatch.
Import ListNotations.

Definition halting_family := machine_of_codes [16;16;16;16;7;7;7;7].
Definition halting_family_tree := Branch 0
  [Cycle true 0 1 0; Cycle false 1 1 0; Cycle false 0 1 0; Cycle false 1 1 0;
   Cycle true 0 1 0; Cycle false 3 1 0; Cycle false 0 1 0; Cycle false 1 1 0;
   Cycle true 0 1 0; Cycle false 3 1 0; Cycle false 0 1 0; Cycle false 1 1 0;
   Cycle true 0 1 0; Cycle false 3 1 0; Cycle false 0 1 0; Cycle false 1 1 0].
Lemma halting_family_checked :
  closed_census_check 33%N 33%N 9 halting_family halting_family_tree = true.
Proof. vm_compute. reflexivity. Qed.
Theorem halting_family_completions : forall tm,
  TM_le halting_family tm -> Bounds 33%N 33%N tm.
Proof. exact (closed_census_check_sound _ _ _ _ _ halting_family_checked). Qed.
Example original_family_halts : stepn halting_family 1 InitES = None.
Proof. reflexivity. Qed.
Example removing_one_defined_choice_is_rejected :
  closed_census_check 33%N 33%N 9 halting_family
    (Branch 0 (repeat (Cycle false 1 1 0) 15)) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions halting_family_completions.
