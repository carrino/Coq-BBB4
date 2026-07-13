(** * TCycler_Corruption: negative controls for the tcycler checkers.

    Same discipline as [Cycle_Corruption]: mutated parameters and
    claims must be rejected.  (An interesting non-negative: enlarging
    the window [W] on [tm_tc_neverqh] still verifies, because a
    translated cycler's trail is shift-periodic, so the extra window
    cells happen to match -- soundness never depends on [W] being
    minimal.  The load-bearing rejections are below.) *)

From BBB4 Require Import BBB4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import TCycler.
From BBB4.Machines Require Import TCycler_Examples.

(* Wrong period. *)
Example tc_corrupt_period :
  tcycler_check_neverqh (mirror_tm tm_tc_neverqh) 771 5 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong side: the machine translates left, the right-handed checker
   on the unmirrored machine must fail. *)
Example tc_corrupt_side :
  tcycler_check_neverqh tm_tc_neverqh 771 6 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong claim type: tm_tc_qh has quiet states, so it is not
   never-quasihalting. *)
Example tc_corrupt_claim :
  tcycler_check_neverqh (mirror_tm tm_tc_qh) 1027 4 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong quiet state: C recurs in the lap. *)
Example tc_corrupt_state :
  tcycler_check_qh (mirror_tm tm_tc_qh) 1027 4 0 StC 2 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong last-visit index, both directions. *)
Example tc_corrupt_lastvisit_hi :
  tcycler_check_qh (mirror_tm tm_tc_qh) 1027 4 0 StA 3 = false.
Proof. vm_compute. reflexivity. Qed.
Example tc_corrupt_lastvisit_lo :
  tcycler_check_qh (mirror_tm tm_tc_qh) 1027 4 0 StA 1 = false.
Proof. vm_compute. reflexivity. Qed.

(* Retargeted machine: the never-QH cycler has no quiet state. *)
Example tc_corrupt_retarget :
  tcycler_check_qh (mirror_tm tm_tc_neverqh) 771 6 0 StA 2 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions tm_tc_neverqh_never_quasihalts.
Print Assumptions tm_tc_qh_decided.
Print Assumptions tm_bbb_sample_never_quasihalts.
