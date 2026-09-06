(** * CensusTr/WalkTr_Frontier: the frontier-split prefix walk.

    Stage 1 of the PARALLEL collection (`make census-tr-frontier`):
    open the tree up a few levels, then serialize BOTH queues -- the
    front (pending TNF nodes, as (machine, pointer) codes) and the
    back (already-deferred candidates).
    tools/censustr/gen_walk_shards.py deals the front round-robin into
    per-process shard drivers; the final deferred list is this
    prefix's back queue plus every shard's.  Deferral is a per-machine
    decision, so the union is exactly the single walk's back queue.

    THREE THINGS THIS FILE GETS RIGHT, each measured after getting it
    wrong:

    1. [SearchQueue_upds q f n] is 2^n pops, not n.  The first version
       ran [Nat.iter 3 q_suc_tr], i.e. 24,576 pops of the FULL ladder
       at ~10 s each -- 1.79 h, to produce a frontier.

    2. Pop with the HALT-ONLY decider ([decider_tr_fast]).  A prefix
       only has to open the tree; deciding nodes is the shards' job,
       and [find_halt] is the only thing a node needs to be expandable
       ([SearchQueue_upd] expands exactly on [R_Halt]).  That took the
       prefix from 6,439 s to milliseconds.

    3. Do NOT shard the front queue of a pop-based walk.  [node_expand]
       pushes children at the FRONT, so popping is depth-first and the
       TAIL of the front queue is never touched: measured 2026-08-24,
       after 32 pops the 48-node frontier still had the completely
       unexpanded root child [1RB---_------_------_------] -- a full
       quarter of the TNF tree -- sitting at index 47.  Its shard ran
       ~17 CPU-hours while the other 47 finished in minutes and 15
       cores sat idle.

    Hence [SearchQueue_levels]: expand EVERY front node once per
    round, so the frontier is a genuine tree level and sibling
    subtrees land in different shards.  Measured level sizes
    (front, back), halt-only decider, all under 0.2 s:

        level 1 -> (24, 2)      level 3 -> (1700, 92)
        level 2 -> (188, 13)    level 4 -> (14608, 879)

    Level 3 is the design point: 1,700 subtrees dealt over ~48 shards
    is ~35 per shard, enough for the size variance to average out,
    while the 92 rows deferred by the weak prefix decider are noise
    against a ~50K list (they are ordinary burn-list entries, and a
    deferred node stands for its whole hole-completion family, so
    burning one clears a subtree).

    NOT part of the default build (exempt); vm_compute is already
    instant here, so the Makefile does not swap in native. *)

From Coq Require Import Arith List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import RunTr.
Import ListNotations.

Set Printing Depth 100000000.
Set Printing Width 250.

Definition FRONTIER_LEVELS : nat := 3.

Time Definition frontier_out
  : (nat * nat) * (list (N * N) * list N) :=
  Eval vm_compute in
    let q := SearchQueue_levels decider_tr_fast FRONTIER_LEVELS q_0_tr in
    (queue_sizes q, (queue_front_encs q, queue_encs q)).

Compute (fst frontier_out).

Compute (fst (snd frontier_out)).

Compute (snd (snd frontier_out)).
