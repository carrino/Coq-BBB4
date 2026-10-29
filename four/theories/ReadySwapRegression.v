(** A reflected oscillator enters the original source graph only after the
    finite target configuration's control state is exchanged. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Symmetry WeightedTail
 ReadyReuse ReadyReuseRegression ReadySwap.
Import ListNotations.
Definition swapped_oscillator := ready_reuse_row [13;16;16;13;14;16;16;14] P123 false 2.
Definition swapped_row := ready_mixed_row swapped_oscillator true.
Example state_exchange_required :
 ready_reuse_check 2%N 2%N proved_oscillator_tail swapped_oscillator=false.
Proof. vm_compute. reflexivity. Qed.
Example exchanged_tail_accepts :
 ready_mixed_check 2%N 2%N proved_oscillator_tail swapped_row=true.
Proof. vm_compute. reflexivity. Qed.
Example exchanged_live_change_rejected :
 ready_mixed_check 2%N 2%N proved_oscillator_tail
   (ready_mixed_row(ready_reuse_row [13;16;16;16;14;16;16;14] P123 false 2)true)=false.
Proof. vm_compute. reflexivity. Qed.
Example exchanged_uncovered_boot_rejected :
 ready_mixed_check 2%N 2%N proved_oscillator_tail
   (ready_mixed_row(ready_reuse_row [13;16;16;13;14;16;16;14] P123 false 0)true)=false.
Proof. vm_compute. reflexivity. Qed.
Theorem exchanged_oscillator_bounds :
 NonHalt(rm_tm swapped_row) /\ Bounds 2%N 2%N(rm_tm swapped_row).
Proof. eapply ready_mixed_sound;[exact oscillator_tail_ready|exact exchanged_tail_accepts]. Qed.
Print Assumptions exchanged_oscillator_bounds.
