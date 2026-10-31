(** A real complementary witness. Marker-only fails its B obligation;
    history-only fails its A obligation, while the separate obligations pass. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline OneStateReach MarkerPotential.
From BBB24Burn3RelaxedMarker Require Import RelaxedMarker.
From BBB24Burn4MarkerComposition Require Import MarkerHistory.
Import ListNotations.
Definition mh_example := machine_of_codes[5;4;10;15;11;14;1;0].
Example mh_A_marker_accepted : mh_marker_A mh_example 2%N 0 1 0=true.
Proof. vm_compute;reflexivity. Qed.
Example mh_uniform_B_reachability_rejected : ore_auto_goal mh_example StB=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_original_marker_checker_rejected : rmp_check mh_example 2%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_wrong_marker_rejected : mh_marker_A mh_example 8%N 0 1 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_insufficient_capacity_rejected : mh_marker_A mh_example 2%N 0 0 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_history_B_accepted : mh_history_target mh_example StB 5 3 4096 16384 32=true.
Proof. vm_compute;reflexivity. Qed.
Example mh_history_A_rank_rejected : mh_history_target mh_example StA 5 3 4096 16384 32=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_zero_width_rejected : mh_history_target mh_example StB 5 0 4096 16384 32=false.
Proof. vm_compute;reflexivity. Qed.
Example mh_empty_exploration_rejected : mh_history_target mh_example StB 5 3 4096 0 32=false.
Proof. vm_compute;reflexivity. Qed.
Theorem mh_example_accepted : mh_check mh_example 2%N 0 1 0 5 3 4096 16384 32=true.
Proof. unfold mh_check;rewrite mh_A_marker_accepted,mh_history_B_accepted;reflexivity. Qed.
Theorem mh_example_nonhalt : NonHalt mh_example.
Proof. exact(proj1(mh_check_sound _ _ _ _ _ _ _ _ _ _ mh_example_accepted)). Qed.
Theorem mh_example_state_zero : QHBound 0 mh_example.
Proof. exact(proj2(mh_check_sound _ _ _ _ _ _ _ _ _ _ mh_example_accepted)). Qed.
Print Assumptions mh_example_state_zero.
