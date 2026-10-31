(** A repeated-word invariant for an expanding interval of fourth symbols.
    Both boundary instructions and both unbounded scans recur. *)
From Coq Require Import NArith List.
From BBB24 Require Import Statement StatementTr Bounds Census RepWLCensus.
Import ListNotations.

Definition fourth_symbol_sweeper : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S3 DR StB)
  | StA, S3 => Some (mkTrans S3 DL StA)
  | StB, S0 => Some (mkTrans S3 DL StA)
  | StB, S3 => Some (mkTrans S3 DR StB)
  | _, _ => None
  end.

Lemma fourth_symbol_sweeper_checked :
  rw_check 0%N 0%N fourth_symbol_sweeper 1 2 0 128 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fourth_symbol_sweeper_bounds :
  NonHalt fourth_symbol_sweeper /\ Bounds 0%N 0%N fourth_symbol_sweeper.
Proof. exact (rw_check_sound _ _ _ _ _ _ _ fourth_symbol_sweeper_checked). Qed.

Theorem fourth_symbol_sweeper_completions : forall tm,
  TM_le fourth_symbol_sweeper tm -> Bounds 0%N 0%N tm.
Proof.
  intros tm Hle. destruct fourth_symbol_sweeper_bounds as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.

Definition broken_fourth_symbol_sweeper : TM := fun q s =>
  match q, s with
  | StA, S3 => None
  | _, _ => fourth_symbol_sweeper q s
  end.

Example reject_halting_scan :
  rw_check 0%N 0%N broken_fourth_symbol_sweeper 1 2 0 128 = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_insufficient_prefix_bound :
  rw_check 0%N 0%N fourth_symbol_sweeper 1 2 1 128 = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_no_closure_fuel :
  rw_check 0%N 0%N fourth_symbol_sweeper 1 2 0 0 = false.
Proof. reflexivity. Qed.

Print Assumptions fourth_symbol_sweeper_completions.
