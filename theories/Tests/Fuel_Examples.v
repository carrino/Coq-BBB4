(** * Fuel_Examples: end-to-end validation of the fuel checker.

    The fuel checker [ngram_check_neverqh_fuel] gates each visited
    state by [lex_ok || runner_ok].  It must therefore accept every
    machine the pure lex checker accepts, with the SAME certificate
    (the runner disjunct is simply never needed).  This re-proves a
    committed bulk machine through the fuel checker to confirm the
    whole pipeline -- seed, gram-set growth, closure, the per-state
    gate, the runner node predicates -- computes end to end under
    [vm_compute] and returns [true] on real input.

    Landing the 62 upstream [neverqh_fuel] machines additionally needs
    the untrusted prover to emit their runner-mode certificates (the
    states the rank measures leave to rule (c2)); the checker they run
    against is the one exercised here. *)

From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Checkers Require Import Fuel.
From BBB4.Machines.Bulk Require Import Bulk_001.
Import ListNotations.

(** The same machine and certificate proven in [Bulk_001] via
    [ngram_check_neverqh_lex_sound], now discharged through the fuel
    checker: the runner alternative is present but unused, so the lex
    certificate still closes it. *)
Theorem nqh_fuel_subsumes_lex :
  NeverQuasiHaltsSt tm_bulk_00001.
Proof.
  apply (ngram_check_neverqh_fuel_sound _ 2 0 528 11 cert_bulk_00001).
  vm_compute. reflexivity.
Qed.
