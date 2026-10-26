From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census CycleCensus.
Import ListNotations.
Example missing_branches_rejected :
  verify scoreN scoreN 9 empty (Branch 0 (repeat Deferred 15)) = false.
Proof. vm_compute. reflexivity. Qed.
Example all_branches_present :
  verify scoreN scoreN 9 empty (Branch 0 (repeat Deferred 16)) = true.
Proof. vm_compute. reflexivity. Qed.
Example invalid_branch_anchor :
  verify scoreN scoreN 9 empty (Branch 1 (repeat Deferred 16)) = false.
Proof. reflexivity. Qed.
Definition drift : TM := fun _ _=>Some(mkTrans S1 DR StA).
Example enormous_bound_early_cycle : cycle_check scoreN scoreN drift false 0 1 0 = true.
Proof. vm_compute. reflexivity. Qed.
Example insufficient_bound_rejected :
  prefix_gate 0%N 0%N drift 1 (fun _=>true) (fun _=>true) = false.
Proof. reflexivity. Qed.
