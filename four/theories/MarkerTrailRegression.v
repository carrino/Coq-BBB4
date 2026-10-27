(** Exit trails permit unrestricted left writes, including a B3 left self-loop.
    The boundary trace checks the blank return and immediate-left exit cases. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape Pipeline StatePipeline
 MarkerState MarkerPotential MarkerTrail.
Import ListNotations.
Definition mt_left_sweep := machine_of_codes[5;10;14;8;7;4;0;13].
Example mt_left_sweep_accepts : mt_check mt_left_sweep 2%N=true.
Proof. vm_compute;reflexivity. Qed.
Example mt_left_sweep_needs_trail : ms_check mt_left_sweep 2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_left_sweep_has_no_weight_drop : mp_check mt_left_sweep 2%N 0 0 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_left_boundary_returns_to_exit :
 csteps mt_left_sweep 4(StB,([],S3,[S1]))=Some(StA,([],S0,[S1;S3;S1])).
Proof. vm_compute;reflexivity. Qed.
Example mt_left_exit_reached_after_reversal :
 csteps mt_left_sweep 2(StB,([S1],S3,[S1]))=Some(StA,([],S0,[S1;S3;S1])).
Proof. vm_compute;reflexivity. Qed.
Example mt_nonexit_right_write_rejects :
 mt_check(machine_of_codes[5;10;14;8;3;4;0;13])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_left_blank_rejects :
 mt_check(machine_of_codes[5;10;14;8;5;4;0;13])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_marked_nonexit_rejects :
 mt_check(machine_of_codes[5;10;14;8;7;5;0;13])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_blank_marker_rejects : mt_check mt_left_sweep 3%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_missing_cell_rejects :
 mt_check(machine_of_codes[5;10;14;8;7;4;0;16])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mt_left_sweep_state_zero : QHBound 0 mt_left_sweep.
Proof. exact(proj2(mt_check_sound _ _ mt_left_sweep_accepts)). Qed.
Example mt_left_sweep_nonhalt : NonHalt mt_left_sweep.
Proof. exact(proj1(mt_check_sound _ _ mt_left_sweep_accepts)). Qed.
