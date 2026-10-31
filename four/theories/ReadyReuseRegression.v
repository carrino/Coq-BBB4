(** Source ranking evidence is reused as an opaque theorem. The target checks
    still reject a changed recurrent rule and an uncovered startup seed. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census NGramRegression
 WeightedRegression WeightedTail Symmetry ReadyReuse.
Import ListNotations.
Definition proved_oscillator_tail :=
 prepared_tail s3_oscillator 1 2 oscillator_graph(fun _=>None).
Lemma oscillator_tail_ready : wt_ready proved_oscillator_tail=true.
Proof. exact(graph_prepares_ready_tail _ _ _ _ _ _ _ graph_accepts_s3). Qed.
Definition renamed_reflected := ready_reuse_row [5;5;16;16;6;6;16;16] P231 true 2.
Example inverse_rename_boot_checked :
 ready_reuse_check 2%N 2%N proved_oscillator_tail renamed_reflected=true.
Proof. vm_compute. reflexivity. Qed.
Example changed_recurring_rule_rejected :
 ready_reuse_check 2%N 2%N proved_oscillator_tail
   (ready_reuse_row [5;16;16;16;6;6;16;16] P231 true 2)=false.
Proof. vm_compute. reflexivity. Qed.
Example uncovered_boot_rejected :
 ready_reuse_check 2%N 2%N proved_oscillator_tail
   (ready_reuse_row [5;5;16;16;6;6;16;16] P231 true 0)=false.
Proof. vm_compute. reflexivity. Qed.
Theorem renamed_reflected_bounds :
 NonHalt(rr_tm renamed_reflected) /\ Bounds 2%N 2%N(rr_tm renamed_reflected).
Proof. eapply ready_reuse_sound;[exact oscillator_tail_ready|exact inverse_rename_boot_checked]. Qed.
Print Assumptions renamed_reflected_bounds.
