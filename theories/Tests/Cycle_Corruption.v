(** * Cycle_Corruption: negative controls for the cycle checkers.

    Mirrors the BBB harness's corruption-test discipline: every
    mutation of a valid certificate's parameters or claim must be
    rejected.  These are [vm_compute] facts about the checkers
    themselves (soundness needs no tests -- it is a theorem -- but a
    checker that accepted everything would make the theorems vacuous;
    these pin down that the accept in [Cycle_Examples] is
    discriminating). *)

From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Machines Require Import Cycle_Examples.

(* Wrong period. *)
Example corrupt_period : cycle_check_neverqh tm_ex_neverqh 8 3 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong claim type: tm_ex_qh has a quiet state, so it is not
   never-quasihalting -- the never-QH checker must refuse it even
   though the loop parameters are right. *)
Example corrupt_claim : cycle_check_neverqh tm_ex_qh 12 4 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong quiet state: C recurs in the loop. *)
Example corrupt_state : cycle_check_qh tm_ex_qh 12 4 StC 4 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong last-visit index, both directions. *)
Example corrupt_lastvisit_hi : cycle_check_qh tm_ex_qh 12 4 StD 5 = false.
Proof. vm_compute. reflexivity. Qed.
Example corrupt_lastvisit_lo : cycle_check_qh tm_ex_qh 12 4 StD 3 = false.
Proof. vm_compute. reflexivity. Qed.

(* Retargeted machine: the never-QH machine has no quiet state at all. *)
Example corrupt_retarget : cycle_check_qh tm_ex_neverqh 8 4 StD 4 = false.
Proof. vm_compute. reflexivity. Qed.

(* The axiom footprint of the end-to-end theorems is exactly
   functional extensionality (printed at build time for the log). *)
Print Assumptions tm_ex_neverqh_never_quasihalts.
Print Assumptions tm_ex_qh_decided.
