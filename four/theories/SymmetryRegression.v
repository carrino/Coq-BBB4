(** Regressions for a non-involutive relabeling, symbol 3, real shadow links,
    and rejection of missing timing/table obligations. *)
From Coq Require Import NArith List.
From BBB24 Require Import Statement StatementTr Spec Bounds Census CycleCensus
  Symmetry Shadow Closeout.
Import ListNotations.

Example three_cycle_symbols :
  map (perm_sym P231) [S0;S1;S2;S3] = [S0;S2;S3;S1].
Proof. reflexivity. Qed.
Example three_cycle_inverse_is_distinct : inverse_perm P231=P312.
Proof. reflexivity. Qed.
Example three_cycle_champion_entry :
  perm_tm P231 champion StA S1=Some (mkTrans S2 DL StB).
Proof. reflexivity. Qed.

Definition shadow_drift : TM := fun q s => match q,s with
  | StA,S0 => Some (mkTrans S0 DL StB)
  | StB,S0 => Some (mkTrans S3 DL StB)
  | _,_ => None
  end.
Definition core_drift : TM := fun q s => match q,s with
  | StA,S0 => Some (mkTrans S2 DR StA)
  | _,_ => None
  end.
Example drift_shadow_link : shadow_check shadow_drift core_drift P132 true=true.
Proof. vm_compute. reflexivity. Qed.
Example drift_core_recurs : cycle_check 0%N 0%N core_drift false 0 1 0=true.
Proof. vm_compute. reflexivity. Qed.
Theorem drift_shadow_all_completions : forall complete,
  TM_le shadow_drift complete -> NonHalt complete /\ Bounds 1%N 1%N complete.
Proof.
  destruct (cycle_check_sound 0%N 0%N core_drift false 0 1 0 drift_core_recurs)
    as [Hnh Hb].
  exact (shadow_check_sound shadow_drift core_drift P132 true 0%N 0%N
    drift_shadow_link Hnh Hb).
Qed.
Example wrong_reflection_rejected : shadow_check shadow_drift core_drift P132 false=false.
Proof. vm_compute. reflexivity. Qed.
Example wrong_symbol_map_rejected : shadow_check shadow_drift core_drift P123 true=false.
Proof. vm_compute. reflexivity. Qed.
Example nonblank_prefix_rejected :
  shadow_check (update shadow_drift StA S0 (Some (mkTrans S1 DL StB)))
    core_drift P132 true=false.
Proof. vm_compute. reflexivity. Qed.
Example same_state_prefix_rejected :
  shadow_check (update shadow_drift StA S0 (Some (mkTrans S0 DL StA)))
    core_drift P132 true=false.
Proof. vm_compute. reflexivity. Qed.
Example additional_core_instruction_rejected :
  shadow_check shadow_drift (update core_drift StA S3 (Some (mkTrans S2 DR StA)))
    P132 true=false.
Proof. vm_compute. reflexivity. Qed.

(** First actual row of the frozen shadow-candidates.tsv inventory.
    This validates the link only; it does not assert a bound for its core. *)
Definition inventory_shadow : TM := fun q s => match q,s with
  | StA,S0 => Some (mkTrans S0 DL StB)
  | StA,S3 => Some (mkTrans S0 DR StA)
  | StB,S0 => Some (mkTrans S1 DR StA)
  | StB,S1 => Some (mkTrans S2 DR StA)
  | StB,S2 => Some (mkTrans S3 DL StB)
  | _,_ => None
  end.
Definition inventory_core : TM := fun q s => match q,s with
  | StA,S0 => Some (mkTrans S1 DL StB)
  | StA,S1 => Some (mkTrans S2 DL StB)
  | StA,S2 => Some (mkTrans S3 DR StA)
  | StB,S0 => Some (mkTrans S0 DR StA)
  | StB,S3 => Some (mkTrans S0 DL StB)
  | _,_ => None
  end.
Example inventory_shadow_link : shadow_check inventory_shadow inventory_core P123 true=true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_shadow_conditional : forall bs bi,
  NonHalt inventory_core -> Bounds bs bi inventory_core ->
  forall complete, TM_le inventory_shadow complete ->
  NonHalt complete /\ Bounds (N.succ bs) (N.succ bi) complete.
Proof.
  intros bs bi Hnh Hb.
  exact (shadow_check_sound inventory_shadow inventory_core P123 true bs bi
    inventory_shadow_link Hnh Hb).
Qed.

Print Assumptions perm_attains_state.
Print Assumptions perm_attains_instruction.
Print Assumptions shadow_check_sound.
