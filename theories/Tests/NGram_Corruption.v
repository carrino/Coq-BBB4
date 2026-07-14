(** * NGram_Corruption: negative controls for the n-gram checker. *)

From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Checkers Require Import NGram.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples NGram_Examples.

(* A quasihalting machine must be rejected: the closure is halt-free
   but state D's liveness fails (its avoiding subgraph keeps the
   loop's cycle). *)
Example ng_reject_qh :
  ngram_check_neverqh tm_ex_qh 2 0 2000 16 = false.
Proof. vm_compute. reflexivity. Qed.

(* The BBB README sample machine at n = 2: the closure closes
   halt-free (96 contexts) but plain acyclicity keeps a spurious
   state-avoiding cycle -- the honest low yield of this decider that
   the upstream docs describe, and what the ranking rules are for. *)
Example ng_reject_sample :
  ngram_check_neverqh (mirror_tm tm_bbb_sample) 2 0 5000 16 = false.
Proof. vm_compute. reflexivity. Qed.

(* Window width 0 is meaningless and guarded out. *)
Example ng_reject_n0 :
  ngram_check_neverqh (mirror_tm tm_tc_neverqh) 0 0 2000 16 = false.
Proof. vm_compute. reflexivity. Qed.

(* Starved search fuel / growth rounds must fail closed. *)
Example ng_reject_fuel :
  ngram_check_neverqh (mirror_tm tm_tc_neverqh) 2 0 3 16 = false.
Proof. vm_compute. reflexivity. Qed.
Example ng_reject_rounds :
  ngram_check_neverqh (mirror_tm tm_bbb_sample) 2 0 5000 0 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions tm_tc_neverqh_never_quasihalts_ngram.
Print Assumptions tm_ex_neverqh_never_quasihalts_ngram.
