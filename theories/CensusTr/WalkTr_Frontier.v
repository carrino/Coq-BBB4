(** * CensusTr/WalkTr_Frontier: the frontier-split prefix walk.

    Stage 1 of the PARALLEL collection (`make census-tr-frontier`):
    run the walk FRONTIER_ITERS rounds from the symmetrized root, then
    serialize BOTH queues -- the front (pending TNF nodes, as
    (machine, pointer) codes) and the back (already-deferred
    candidates).  tools/censustr/gen_walk_shards.py partitions the
    front round-robin into per-process shard drivers; the final
    deferred list is this prefix's back queue plus every shard's.
    Deferral is a per-machine decision, so the union is exactly the
    single walk's back queue.

    NOT part of the default build (exempt, like WalkTr_Collect.v);
    the Makefile seds FRONTIER_ITERS and the evaluator in. *)

From Coq Require Import Arith List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Set Printing Depth 100000000.
Set Printing Width 250.

Definition FRONTIER_ITERS : nat := 3.

Time Definition frontier_out
  : (nat * nat) * (list (N * N) * list N) :=
  Eval vm_compute in
    let q := Nat.iter FRONTIER_ITERS q_suc_tr q_0_tr in
    (queue_sizes q, (queue_front_encs q, queue_encs q)).

Compute (fst frontier_out).

Compute (fst (snd frontier_out)).

Compute (snd (snd frontier_out)).
