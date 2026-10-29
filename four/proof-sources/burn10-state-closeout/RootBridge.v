(** Conditional global bridge. The two exhaustive root bounds are explicit
    hypotheses; this file does not claim either root has been closed out. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Pipeline StateOnlyCloseout
  FamilyIndex Symmetry.
From BBB24Burn10StateCensus Require Import StateCensus.
Import ListNotations.

Definition blank_root := machine_of_codes [1;16;16;16;16;16;16;16].
Definition nonblank_root := machine_of_codes [5;16;16;16;16;16;16;16].
Definition root_board := [blank_root; nonblank_root].
Definition root_index := family_index root_board.

Definition blank_leaf mirrored := StateLeaf StateLookup
  (state_lookup (family_key blank_root) P123 mirrored).
Definition nonblank_leaf permutation mirrored := StateLeaf StateLookup
  (state_lookup (family_key nonblank_root) permutation mirrored).
Definition drift_leaf mirrored := StateCycle StateLookup mirrored 0 1 0.

Definition root_certificate := StateBranch StateLookup 0 [
  drift_leaf true; blank_leaf false; drift_leaf false; blank_leaf true;
  drift_leaf true; nonblank_leaf P123 false; drift_leaf false; nonblank_leaf P123 true;
  drift_leaf true; nonblank_leaf P213 false; drift_leaf false; nonblank_leaf P213 true;
  drift_leaf true; nonblank_leaf P321 false; drift_leaf false; nonblank_leaf P321 true].

Lemma root_certificate_checked :
  state_verify scoreN StateLookup (state_lookup_check root_index) 2 empty root_certificate = true.
Proof. vm_compute. reflexivity. Qed.

Local Opaque scoreN.
Theorem two_root_state_upper :
  StateBoardSound score root_board -> forall tm, QHBound score tm.
Proof.
  intros Hroot.
  exact (state_census_upper scoreN StateLookup (state_lookup_check root_index)
    (fun family witness => state_lookup_sound score root_board family witness Hroot)
    2 root_certificate root_certificate_checked).
Qed.
Local Transparent scoreN.

Example missing_child_rejected :
  state_verify scoreN StateLookup (state_lookup_check root_index) 2 empty
    (StateBranch StateLookup 0 []) = false.
Proof. vm_compute. reflexivity. Qed.

Example halting_budget_required :
  state_verify 0%N StateLookup (state_lookup_check root_index) 2 empty root_certificate = false.
Proof. reflexivity. Qed.

Example empty_lookup_rejects_nonblank_root :
  state_verify scoreN StateLookup (state_lookup_check (family_index [])) 1 nonblank_root
    (nonblank_leaf P123 false) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions two_root_state_upper.
