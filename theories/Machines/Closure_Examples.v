(** * Closure_Examples: the closure engine on concrete machines.

    The exact-configuration instance needs no cycle parameters at
    all: given only a step index [t] (here even 0) and a search fuel,
    it explores the reachable normalized configuration set and proves
    never-quasihalting by per-state rank liveness.

    [tm_ex_neverqh] is the in-place cycler from [Cycle_Examples];
    [tm_tc_neverqh] (via [mirror_tm]) is a translated cycler whose
    trail is all-blank, so its *normalized* head-relative
    configuration set is also finite -- the exact closure covers
    blank-trail translated cyclers for free. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape Closure Mirror.
From BBB4.Checkers Require Import ExactClosure.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples.
Import ListNotations.

(** The in-place cycler, decided with no [(n1, p)] parameters. *)
Theorem tm_ex_neverqh_never_quasihalts_closure :
  NeverQuasiHaltsSt tm_ex_neverqh.
Proof.
  apply (exact_closure_check_neverqh_sound _ 0 100).
  vm_compute. reflexivity.
Qed.

(** The blank-trail translated cycler, likewise parameter-free
    (compare [tm_tc_neverqh_never_quasihalts], which needed the
    anchor/period/reach certificate data). *)
Theorem tm_tc_neverqh_never_quasihalts_closure :
  NeverQuasiHaltsSt tm_tc_neverqh.
Proof.
  apply mirror_never_qh.
  apply (exact_closure_check_neverqh_sound _ 0 300).
  vm_compute. reflexivity.
Qed.
