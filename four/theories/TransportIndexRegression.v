From Coq Require Import List NArith FSets.FMapPositive.
From BBB24 Require Import Statement Census Closeout Pipeline Symmetry
  FamilyIndex ConjugateTransport IndexedConjugate.
Import ListNotations.

(** A nonblank meeting at different prefix lengths, taken from the pilot. *)
Definition regression_target := machine_of_codes [5;0;16;11;14;11;1;13].
Definition regression_source := machine_of_codes [5;6;2;8;14;8;16;16].
Definition regression_row := indexed_conjugate_row [5;0;16;11;14;11;1;13]
  (family_key regression_source) P321 true 14 8.
Example nonblank_meeting : meet_check regression_target 14 8=true.
Proof. vm_compute. reflexivity. Qed.
Example wrong_meeting_rejected : meet_check regression_target 13 8=false.
Proof. vm_compute. reflexivity. Qed.
Example indexed_relation_checked :
  indexed_conjugate_check 4097%N 4097%N 8192%N 8192%N
    (family_index [regression_source]) regression_row=true.
Proof. vm_compute. reflexivity. Qed.
Example prefix_cost_required :
  indexed_conjugate_check 4097%N 4097%N 4097%N 4097%N
    (family_index [regression_source]) regression_row=false.
Proof. vm_compute. reflexivity. Qed.
Example missing_source_rejected :
  indexed_conjugate_check 4097%N 4097%N 8192%N 8192%N
    (family_index []) regression_row=false.
Proof. vm_compute. reflexivity. Qed.
Example incompatible_completion_rejected :
  indexed_completion_check (family_index [regression_source])
    (family_key regression_source) regression_target=false.
Proof. vm_compute. reflexivity. Qed.
Example symbol_three_changes_key :
  Pos.eqb (family_key (machine_of_codes [5;0;16;11;14;11;1;13]))
    (family_key (machine_of_codes [5;0;16;11;14;11;1;9]))=false.
Proof. vm_compute. reflexivity. Qed.
