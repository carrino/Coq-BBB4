(** * CensusTr/WalkTr_Frontier: the frontier-split prefix walk.

    Stage 1 of the PARALLEL collection (`make census-tr-frontier`):
    pop a SMALL number of nodes to open the tree up, then serialize
    BOTH queues -- the front (pending TNF nodes, as (machine, pointer)
    codes) and the back (already-deferred candidates).
    tools/censustr/gen_walk_shards.py partitions the front round-robin
    into per-process shard drivers; the final deferred list is this
    prefix's back queue plus every shard's.  Deferral is a per-machine
    decision, so the union is exactly the single walk's back queue.

    TWO THINGS THIS FILE GETS RIGHT, both measured 2026-08-23 after
    getting them wrong:

    1. [SearchQueue_upds q f n] is 2^n pops, not n.  The first version
       ran [Nat.iter 3 q_suc_tr], i.e. 24,576 pops of the FULL ladder
       at ~10 s each -- hours, to produce a frontier.

    2. The front queue is a WORKING SET, not a level of the tree: it
       saturates at ~48 nodes after ~32 pops and stays there no matter
       how deep the prefix goes, while the back queue grows linearly.
       So a deeper prefix buys NO extra shards and only dumps more
       machines into the list decided by a weaker tier.

    Hence: 2^5 = 32 pops of the halt-only decider ([decider_tr_fast]),
    which yields front 48 / back 27 in milliseconds.  48 shards is
    three comfortable waves on 16 cores, and 27 weakly-decided rows is
    noise against a ~50K list.

    NOT part of the default build (exempt); vm_compute is already
    instant here, so the Makefile does not swap in native. *)

From Coq Require Import Arith List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Set Printing Depth 100000000.
Set Printing Width 250.

Definition FRONTIER_POPS : nat := 5.   (* 2^5 = 32 pops *)

Time Definition frontier_out
  : (nat * nat) * (list (N * N) * list N) :=
  Eval vm_compute in
    let q := SearchQueue_upds q_0_tr decider_tr_fast FRONTIER_POPS in
    (queue_sizes q, (queue_front_encs q, queue_encs q)).

Compute (fst frontier_out).

Compute (fst (snd frontier_out)).

Compute (snd (snd frontier_out)).
