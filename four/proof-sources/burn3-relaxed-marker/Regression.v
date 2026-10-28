(** The new case turns left on marked1 without immediately entering A.
    Independent failures exercise preservation, capacity and totality gates. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape Census Pipeline StatePipeline
  MarkerState MarkerPotential.
From BBB24Burn3RelaxedMarker Require Import RelaxedMarker.
Import ListNotations.
Definition rmp_example := machine_of_codes[5;10;10;6;11;13;1;12].
Example rmp_example_accepted : rmp_check rmp_example 10%N 1 1 0=true.
Proof. vm_compute;reflexivity. Qed.
Example rmp_original_marker_rejected : mp_check rmp_example 10%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_marked_left_move_stays_B : rmp_example StB S1=Some(mkTrans S3 DL StB).
Proof. reflexivity. Qed.
Example rmp_missing_rewritten_marker_rejected : rmp_check rmp_example 2%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_missing_initial_marker_rejected : rmp_check rmp_example 8%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_blank_marker_rejected : rmp_check rmp_example 11%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_missing_left_drop_rejected : rmp_check rmp_example 10%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_excess_right_growth_rejected : rmp_check rmp_example 10%N 1 2 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_excess_weight_rejected : rmp_check rmp_example 10%N 5 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_marked_right_escape_rejected :
 rmp_check(machine_of_codes[5;10;10;6;11;15;1;12])10%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_partial_table_rejected :
 rmp_check(machine_of_codes[5;10;10;16;11;13;1;12])10%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example rmp_missing_B_recurrence_rejected :
 rmp_check(machine_of_codes[4;10;10;6;11;13;1;12])10%N 1 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Theorem rmp_example_nonhalt : NonHalt rmp_example.
Proof. exact(proj1(rmp_check_sound _ _ _ _ _ rmp_example_accepted)). Qed.
Theorem rmp_example_state_zero : QHBound 0 rmp_example.
Proof. exact(proj2(rmp_check_sound _ _ _ _ _ rmp_example_accepted)). Qed.
Print Assumptions rmp_example_state_zero.
