(** * CensusTr/WalkTr_Collect_A1: shard A1 of the 4-way transition-level
    COLLECTION walk (subtree rooted at [child S1 DR StA]).

    NOT part of the default build (like WalkTr_Collect.v): run all four
    shards via `make census-tr-collect-shards` (box, native_compute,
    one process per shard).  The four subtree back queues concatenate
    to the single-walk back queue -- deferral is a per-machine decision,
    so processing order cannot change the set.  See WalkTr_Collect.v
    for the serialization rationale. *)

From Coq Require Import Arith List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Set Printing Depth 100000000.
Set Printing Width 250.

Definition WALK_TR_ITERS : nat := 4096.

Time Definition walk_tr_out : (nat * nat) * list N :=
  Eval vm_compute in
    let q := Nat.iter WALK_TR_ITERS q_suc_tr (q_sub_tr S1 StA) in
    (queue_sizes q, queue_encs q).

Compute (fst walk_tr_out).

Compute (snd walk_tr_out).
