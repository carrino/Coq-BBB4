(** * CensusTr/WalkTr_Collect: the transition-level COLLECTION walk driver.

    NOT part of the default build (deliberately absent from
    _CoqProject): run it on demand via `make census-tr-collect` (box,
    native_compute under the census opam switch -- the Makefile swaps
    the evaluator in) or `make census-tr-collect-vm` (any coqc;
    measured ~1.4 ms/pop, whole tree a few hours).

    4096 rounds x up to 8192 pops covers the 3,995,005-node tree with
    slack; iterating past queue exhaustion is a no-op, so the constant
    only needs to be big enough.  The output to capture is the stdout:

    - [queue_sizes]: (front, back).  front = 0 means the walk
      completed; back = the number of deferred candidates.
    - [queue_encs]: the deferred candidates as decimal [tm_enc] codes;
      tools/censustr/decode_enc.py turns them into bbchallenge machine
      text (and, later, generated DeferredTr tables). *)

From Coq Require Import Arith List NArith.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Definition WALK_TR_ITERS : nat := 4096.

Time Definition walk_tr : SearchQueue :=
  Eval vm_compute in Nat.iter WALK_TR_ITERS q_suc_tr q_0_tr.

Compute queue_sizes walk_tr.

Compute queue_encs walk_tr.
