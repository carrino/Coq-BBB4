(** Positive controls and independent failures for entry, B-preservation,
    capacity, totality and the other state's recurrence requirement. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape Census Pipeline StatePipeline
  MarkerState MarkerPotential.
From BBB24Burn4EntryMarker Require Import EntryMarker.
Import ListNotations.
Definition em_example := machine_of_codes[5;8;10;6;11;14;1;0].
Example em_example_accepted : em_check em_example 2%N 0 1 0=true.
Proof. vm_compute;reflexivity. Qed.
Example em_A_only_rewrite_allowed : em_cell em_example(ms_mark 2%N)StA S1=true.
Proof. vm_compute;reflexivity. Qed.
Example em_old_marker_rejected_at_these_parameters : mp_check em_example 2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Definition em_marked_left_example := machine_of_codes[5;10;10;6;11;13;1;12].
Example em_marked_left_accepted : em_check em_marked_left_example 10%N 1 1 0=true.
Proof. vm_compute;reflexivity. Qed.
Example em_right_entry_rejected :
 em_check(machine_of_codes[7;8;10;6;11;14;1;0])2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_unmarked_entry_rejected :
 em_check(machine_of_codes[9;8;10;6;11;14;1;0])2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_marked_right_B_escape_rejected :
 em_check(machine_of_codes[5;8;10;6;11;7;1;0])2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_marker_erasure_rejected_despite_capacity :
 mp_rank_check(machine_of_codes[5;8;10;6;11;1;1;0])(mp_weights 1 1 0)=true /\
 em_check(machine_of_codes[5;8;10;6;11;1;1;0])2%N 1 1 0=false.
Proof. vm_compute;split;reflexivity. Qed.
Example em_missing_left_drop_rejected : em_check em_example 2%N 0 0 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_excess_right_growth_rejected : em_check em_example 2%N 0 2 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_excess_weight_rejected : em_check em_example 2%N 5 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_partial_table_rejected :
 em_check(machine_of_codes[5;8;10;16;11;14;1;0])2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example em_missing_B_recurrence_rejected_despite_marker_and_capacity :
 let tm:=machine_of_codes[5;4;10;6;11;14;1;0]in
 em_preserve tm(ms_mark 2%N)=true /\
 mp_rank_check tm(mp_weights 0 1 0)=true /\ em_check tm 2%N 0 1 0=false.
Proof. vm_compute;repeat split;reflexivity. Qed.
Example em_blank_marker_rejected : em_check em_example 3%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Theorem em_example_nonhalt : NonHalt em_example.
Proof. exact(proj1(em_check_sound _ _ _ _ _ em_example_accepted)). Qed.
Theorem em_example_state_zero : QHBound 0 em_example.
Proof. exact(proj2(em_check_sound _ _ _ _ _ em_example_accepted)). Qed.
Print Assumptions em_example_state_zero.
