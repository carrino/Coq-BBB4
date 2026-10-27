(** A left-writing cycle is harmless when two checked walls confine it. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape Pipeline StatePipeline
 MarkerState MarkerPotential MarkerTrail MarkerWalls.
Import ListNotations.
Definition mw_two_cycle := machine_of_codes[5;10;10;2;15;6;13;9].
Example mw_two_cycle_accepts : mw_check mw_two_cycle 2%N=true.
Proof. vm_compute;reflexivity. Qed.
Example mw_two_cycle_needs_walls : ms_check mw_two_cycle 2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_two_cycle_has_no_weight_drop : mp_check mw_two_cycle 2%N 0 0 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_two_cycle_has_no_exit_trail : mt_check mw_two_cycle 2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_left_wall_not_initially_available : mw_leftb(ms_mark 2%N)c0=false.
Proof. reflexivity. Qed.
Example mw_boot_establishes_left_wall : mw_boot mw_two_cycle(ms_mark 2%N)=true.
Proof. vm_compute;reflexivity. Qed.
Example mw_boot_configuration : csteps mw_two_cycle 2 c0=Some(StB,([S3],S1,[])).
Proof. vm_compute;reflexivity. Qed.
Example mw_bad_marked_write_rejects :
 mw_check(machine_of_codes[5;10;10;2;15;10;13;9])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_bad_left_state_rejects :
 mw_check(machine_of_codes[5;10;8;2;15;6;13;9])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_bad_right_rank_rejects :
 mw_check(machine_of_codes[5;10;10;2;3;6;13;9])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_empty_boot_mask_rejects : mw_boot mw_two_cycle(ms_mark 0%N)=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_missing_cell_rejects :
 mw_check(machine_of_codes[5;10;10;2;15;6;13;16])2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mw_two_cycle_state_zero : QHBound 0 mw_two_cycle.
Proof. exact(proj2(mw_check_sound _ _ mw_two_cycle_accepts)). Qed.
Example mw_two_cycle_nonhalt : NonHalt mw_two_cycle.
Proof. exact(proj1(mw_check_sound _ _ mw_two_cycle_accepts)). Qed.
