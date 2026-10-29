(** Undefined unreachable A cells are allowed; undefined B cells and blank
    markers are still rejected before any graph is constructed. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline MarkerPotential MarkerState
 OneStateReach OneStateConditional.
From BBB24Burn9ContextMarker Require Import ContextMarker.
From BBB24Burn10MarkerHistory Require Import PartialContextMarker.
Import ListNotations.
Definition partial := machine_of_codes [5;4;16;9;11;6;1;11].
Example partial_table_not_total : cm_total partial=false.
Proof. vm_compute;reflexivity. Qed.
Example original_uniform_B_rejects : ore_auto_goal partial StB=false.
Proof. vm_compute;reflexivity. Qed.
Example conditional_B_accepts : ore_auto_goal(orc_fill_goal partial StB)StB=true.
Proof. vm_compute;reflexivity. Qed.
Example blank_marker_rejected : pm_check partial 3%N 0 1 0 4 4 4096 131072 128=false.
Proof. vm_compute;reflexivity. Qed.
Definition missing_B0 := machine_of_codes[5;4;16;9;16;6;1;11].
Example undefined_B_is_rejected : pm_check missing_B0 2%N 0 1 0 4 4 4096 131072 128=false.
Proof. vm_compute;reflexivity. Qed.
