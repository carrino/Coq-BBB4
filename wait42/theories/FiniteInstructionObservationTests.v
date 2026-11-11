(** Small executable regressions for inclusive instruction observations.
    Each soundness example applies to every TM_le completion of its input. *)
From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec ControlRank FiniteInstructionObservation.
Import ListNotations.

Module FiniteInstructionObservationRegression.
Definition empty_inv (_ : St) := false.

(** Slot trace at indices 0..8: A0 B0 D0 C1 C1 C0 B1 A1 D1.
    D1 is undefined, so the partial run has no configuration at index 9.
    Its D1 configuration still counts under the FiresAt convention. *)
Definition all_eight_then_halt : TM := fun q h => match q,h with
 | StA,S0 => Some (mkTrans S1 DL StB)
 | StA,S1 => Some (mkTrans S0 DL StD)
 | StB,S0 => Some (mkTrans S1 DL StD)
 | StB,S1 => Some (mkTrans S1 DR StA)
 | StC,S0 => Some (mkTrans S0 DR StB)
 | StC,S1 => Some (mkTrans S1 DL StC)
 | StD,S0 => Some (mkTrans S1 DR StC)
 | StD,S1 => None end.

Example inclusive_endpoint_completes_all_eight :
 finite_instruction_observation_check all_eight_then_halt empty_inv 0%N 8%N = true.
Proof. vm_compute. reflexivity. Qed.
Example too_short_misses_last_instruction :
 finite_instruction_observation_check all_eight_then_halt empty_inv 0%N 7%N = false.
Proof. vm_compute. reflexivity. Qed.
Example partial_run_actually_halts : csteps all_eight_then_halt 9 c0 = None.
Proof. vm_compute. reflexivity. Qed.
Example all_eight_survive_absent_endpoint :
 fst (instruction_observation_window all_eight_then_halt 0%N 9%N) = None /\
 finite_instruction_observation_check all_eight_then_halt empty_inv 0%N 9%N = true.
Proof. vm_compute. split; reflexivity. Qed.
Example all_eight_partial_halting_completion_safe : forall tm',
 TM_le all_eight_then_halt tm' -> WindowBoundTr tm' 0 9.
Proof.
 intros tm' Hle.
 exact (finite_instruction_observation_check_completion all_eight_then_halt empty_inv
   0%N 9%N (proj2 all_eight_survive_absent_endpoint) tm' Hle).
Qed.
Example inclusive_all_eight_completion_safe : forall tm',
 TM_le all_eight_then_halt tm' -> WindowBoundTr tm' 0 8.
Proof.
 intros tm' Hle.
 exact (finite_instruction_observation_check_completion all_eight_then_halt empty_inv
   0%N 8%N inclusive_endpoint_completes_all_eight tm' Hle).
Qed.

(** A0 seeds a one, after which B oscillates between its two slots.
    The invariant is the four-bit state mask {B}, not a slot mask. *)
Definition tail_machine : TM := fun q h => match q,h with
 | StA,S0 => Some (mkTrans S1 DR StB)
 | StB,S0 => Some (mkTrans S0 DL StB)
 | StB,S1 => Some (mkTrans S1 DR StB)
 | _,_ => None end.
Definition just_B q := st_eqb q StB.
Example closed_state_tail_both_symbols_observed :
 finite_instruction_observation_check tail_machine just_B 1%N 1%N = true.
Proof. vm_compute. reflexivity. Qed.
Example closed_state_tail_missing_symbol_rejected :
 finite_instruction_observation_check tail_machine just_B 1%N 0%N = false.
Proof. vm_compute. reflexivity. Qed.
Example tail_branch_does_not_need_all_eight :
 all_instruction_bits (snd (instruction_observation_window tail_machine 1%N 1%N)) = false.
Proof. vm_compute. reflexivity. Qed.
Example tail_completion_safe : forall tm', TM_le tail_machine tm' ->
 WindowBoundTr tm' 1 1.
Proof.
 intros tm' Hle.
 exact (finite_instruction_observation_check_completion tail_machine just_B
   1%N 1%N closed_state_tail_both_symbols_observed tm' Hle).
Qed.

Definition undefined_tail_machine : TM := fun q h => match q,h with
 | StA,S0 => Some (mkTrans S1 DR StB)
 | StB,S0 => Some (mkTrans S0 DL StB)
 | _,_ => None end.
Example undefined_slot_never_closes_family :
 cr_closed_ok undefined_tail_machine just_B = false /\
 finite_instruction_observation_check undefined_tail_machine just_B 1%N 1%N = false.
Proof. vm_compute. split; reflexivity. Qed.
Example undefined_slot_was_observed_at_actual_endpoint :
 instruction_bit_get (StB,S1)
  (snd (instruction_observation_window undefined_tail_machine 1%N 1%N)) = true.
Proof. vm_compute. reflexivity. Qed.

Definition tail_entry := mkInstructionObservationCase tail_machine just_B 1%N.
Example equal_width_gate : instruction_observation_batch_check [tail_entry] 1%N 1%N = true.
Proof. vm_compute. reflexivity. Qed.
Example wider_width_gate : instruction_observation_batch_check [tail_entry] 1%N 2%N = true.
Proof. vm_compute. reflexivity. Qed.
Example too_narrow_global_width_rejected :
 instruction_observation_batch_check [tail_entry] 1%N 0%N = false.
Proof. vm_compute. reflexivity. Qed.
Example checked_widening_completion_safe : forall tm', TM_le tail_machine tm' ->
 WindowBoundTr tm' 1 2.
Proof.
 intros tm' Hle.
 exact (instruction_observation_batch_completion [tail_entry] 1%N 2%N
   wider_width_gate tail_entry (or_introl eq_refl) tm' Hle).
Qed.

End FiniteInstructionObservationRegression.
Print Assumptions FiniteInstructionObservationRegression.all_eight_partial_halting_completion_safe.
Print Assumptions FiniteInstructionObservationRegression.tail_completion_safe.
Print Assumptions FiniteInstructionObservationRegression.checked_widening_completion_safe.
