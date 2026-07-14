(** * NGram_Examples: the n-gram CPS checker on concrete machines.

    Both machines are decided by the abstraction alone -- no cycle
    parameters, just a window width [n] (and here not even a
    simulated prefix, [t = 0]): the translated cycler through its
    mirror, and the in-place cycler directly.  Compare the same
    machines' earlier proofs, which needed anchor/period data. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Checkers Require Import NGram.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples.
Import ListNotations.

Theorem tm_tc_neverqh_never_quasihalts_ngram :
  NeverQuasiHaltsSt tm_tc_neverqh.
Proof.
  apply mirror_never_qh.
  apply (ngram_check_neverqh_sound _ 2 0 2000 16).
  vm_compute. reflexivity.
Qed.

Theorem tm_ex_neverqh_never_quasihalts_ngram :
  NeverQuasiHaltsSt tm_ex_neverqh.
Proof.
  apply (ngram_check_neverqh_sound _ 2 0 2000 16).
  vm_compute. reflexivity.
Qed.
