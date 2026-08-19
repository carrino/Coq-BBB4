(** * CensusTr/WalkTr_Collect: the transition-level COLLECTION walk driver.

    NOT part of the default build (deliberately absent from
    _CoqProject): run it on demand via `make census-tr-collect` (box,
    native_compute under the census opam switch -- the Makefile swaps
    the evaluator in) or `make census-tr-collect-vm` (any coqc).

    4096 rounds x up to 8192 pops covers the 3,995,005-node tree with
    slack; iterating past queue exhaustion is a no-op, so the constant
    only needs to be big enough.

    The walk result is SERIALIZED INSIDE the evaluation: storing the
    raw queue would read back and kernel-typecheck ~400K [TNF_Node]s
    each carrying a reified transition-table lambda -- measured on the
    box as tens of minutes and gigabytes AFTER an 8.5-minute walk.
    [(queue_sizes q, queue_encs q)] is scalars and [N] codes only, so
    readback is cheap.  (The state census avoids materialization
    entirely by proving [= ([], [])]; a collection walk needs the data
    out, so it serializes instead.)

    The output to capture is the stdout:

    - first Compute, [queue_sizes]: (front, back).  front = 0 means
      the walk completed; back = the number of deferred candidates.
    - second Compute, [queue_encs]: the deferred candidates as decimal
      [tm_enc] codes; tools/censustr/decode_enc.py turns them into
      bbchallenge machine text (and, later, generated DeferredTr
      tables). *)

From Coq Require Import Arith List NArith.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Set Printing Depth 100000000.
Set Printing Width 250.

Definition WALK_TR_ITERS : nat := 4096.

Time Definition walk_tr_out : (nat * nat) * list N :=
  Eval vm_compute in
    let q := Nat.iter WALK_TR_ITERS q_suc_tr q_0_tr in
    (queue_sizes q, queue_encs q).

Compute (fst walk_tr_out).

Compute (snd walk_tr_out).
