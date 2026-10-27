(** Positive modes and fail-closed gates of the state-only marker checker. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline StatePipeline OneStateReach MarkerState.
Import ListNotations.
Definition ms_rank_example := stp_machine 3602778504%N.
Definition ms_right_example := stp_machine 6430409601%N.
Example ms_rank_example_accepts : ms_check ms_rank_example 2%N=true.
Proof. vm_compute;reflexivity. Qed.
Example ms_rank_example_needs_rank : ms_right_check ms_rank_example=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_right_example_accepts : ms_check ms_right_example 2%N=true.
Proof. vm_compute;reflexivity. Qed.
Example ms_right_example_has_cyclic_writes :
 ms_rank_check ms_right_example(ore_rank_walk ms_right_example StA 4)=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_blank_marker_rejects : ms_check ms_rank_example 1%N=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_missing_cell_rejects :
 ms_check(machine_of_codes[5;10;6;16;7;4;13;8])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_left_blank_sweep_rejects :
 ms_check(machine_of_codes[5;4;0;9;13;6;11;15])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_nonexiting_marked_cell_rejects :
 ms_check(machine_of_codes[5;10;6;3;7;5;13;8])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_bad_left_return_rejects :
 ms_check(machine_of_codes[5;10;6;3;7;4;1;8])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example ms_all_nonblank_mask :
 (ms_mark 14%N S0,ms_mark 14%N S1,ms_mark 14%N S2,ms_mark 14%N S3)=
 (false,true,true,true).
Proof. reflexivity. Qed.
Example ms_rank_example_state_zero : QHBound 0 ms_rank_example.
Proof. exact(proj2(ms_check_sound _ _ ms_rank_example_accepts)). Qed.
Example ms_right_example_nonhalt : NonHalt ms_right_example.
Proof. exact(proj1(ms_check_sound _ _ ms_right_example_accepts)). Qed.
