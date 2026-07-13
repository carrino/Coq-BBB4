(** * Closure_Corruption: negative controls for the closure engine. *)

From BBB4 Require Import BBB4_Statement CTape Closure Mirror.
From BBB4.Checkers Require Import ExactClosure.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples Closure_Examples.

(* A quasihalting machine must be rejected: state D goes quiet, so
   the D-avoiding subgraph keeps the loop's cycle and no rank
   exists. *)
Example cl_reject_qh :
  exact_closure_check_neverqh tm_ex_qh 0 200 = false.
Proof. vm_compute. reflexivity. Qed.

(* A nonblank-trail translated cycler has an infinite exact closure:
   the search must exhaust its fuel and fail (honest incompleteness
   of this instance; the machine itself is never-QH and is proved so
   by the TCycler checker). *)
Example cl_reject_growing :
  exact_closure_check_neverqh (mirror_tm tm_bbb_sample) 0 500 = false.
Proof. vm_compute. reflexivity. Qed.

(* Zero fuel: the search cannot even start. *)
Example cl_reject_fuel :
  exact_closure_check_neverqh tm_ex_neverqh 0 0 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions tm_ex_neverqh_never_quasihalts_closure.
Print Assumptions tm_tc_neverqh_never_quasihalts_closure.
