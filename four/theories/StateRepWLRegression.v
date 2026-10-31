(** State acceptance is deliberately weaker than instruction acceptance. *)
From Coq Require Import NArith.
From BBB24 Require Import Statement Spec Census StateOnlyCloseout RepWLCensus StateRepWL.
Definition srw_oscillator : TM := fun q s =>
  match q,s with
  | StA,S0 | StA,S3 => Some (mkTrans S3 DR StB)
  | StB,S0 | StB,S3 => Some (mkTrans S3 DL StA)
  | _,_=>None end.
Example srw_oscillator_checked : srw_check 0%N srw_oscillator 1 2 0 128=true.
Proof. vm_compute. reflexivity. Qed.
Example srw_oscillator_instruction_zero_rejected : rw_check 0%N 0%N srw_oscillator 1 2 0 128=false.
Proof. vm_compute. reflexivity. Qed.
Example srw_halt_rejected : srw_check 0%N (fun _ _=>None) 1 2 0 128=false.
Proof. vm_compute. reflexivity. Qed.
Example srw_prefix_rejected : srw_check 0%N srw_oscillator 1 2 1 128=false.
Proof. vm_compute. reflexivity. Qed.
Example srw_no_fuel_rejected : srw_check 0%N srw_oscillator 1 2 0 0=false.
Proof. reflexivity. Qed.
Theorem srw_partial_all_completions : forall tm,
  TM_le srw_oscillator tm -> QHBound 0 tm.
Proof.
  intros tm Hle. destruct (srw_check_sound 0%N srw_oscillator 1 2 0 128 srw_oscillator_checked) as [Hnh Hb].
  eapply state_bound_extend; eauto.
Qed.
Print Assumptions srw_partial_all_completions.
