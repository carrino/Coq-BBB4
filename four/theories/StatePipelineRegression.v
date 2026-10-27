(** State-only finite/history checks, partial-table packing, and mode separation. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Pipeline StateOnlyCloseout
  FiniteCensus StatePipeline.
Import ListNotations.
Definition stp_oscillator := machine_of_codes [15;16;16;15;12;16;16;12].
Example stp_finite_accepts_state :
  stp_check 0%N stp_oscillator (StateFinite 2 0 128 4)=true.
Proof. vm_compute. reflexivity. Qed.
Example stp_history_accepts_state :
  stp_check 0%N stp_oscillator (StateHistory 1 2 0 128 4)=true.
Proof. vm_compute. reflexivity. Qed.
Example stp_same_graph_rejects_instruction_zero :
  fn_check_mode false 0%N 0%N stp_oscillator 2 0 128 4=false.
Proof. vm_compute. reflexivity. Qed.
Example stp_rejects_halting :
  stp_check 0%N (fun _ _=>None) (StateFinite 2 0 128 4)=false.
Proof. vm_compute. reflexivity. Qed.
Example stp_rejects_prefix_past_bound :
  stp_check 0%N stp_oscillator (StateHistory 1 2 1 128 4)=false.
Proof. vm_compute. reflexivity. Qed.
Example stp_partial_packing_roundtrip : stp_machine 5334063750%N=stp_oscillator.
Proof. vm_compute. reflexivity. Qed.
Theorem stp_partial_all_completions : forall tm,
  TM_le stp_oscillator tm -> QHBound 0 tm.
Proof.
  intros tm Hle. eapply state_bound_extend; [| |exact Hle];
  destruct (stp_check_sound 0%N stp_oscillator (StateFinite 2 0 128 4)
    stp_finite_accepts_state); assumption.
Qed.
Print Assumptions stp_partial_all_completions.
