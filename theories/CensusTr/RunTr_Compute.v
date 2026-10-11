(** * Instruction census computation without proven-board libraries.

    Native units need machine tables and the decider, not the board
    proofs. RunTr keeps the original lists and proofs and reattaches them
    to the data lists by kernel conversion. Every proof remains a
    prerequisite of the final census assembly. *)
From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import TNF_QHTr DecideTr DeferredTr_Data
  ProvTr_Data ProvQHTr_Data.
Import ListNotations.

Definition B_tr : nat := 32779478.
Definition D_tr : list TM := D_censusTr.

(** the same rung ladders as the state census (Run_Compute.v), and the
    same n-gram fuel/rounds *)
Definition ng_rungs_tr : list (nat * nat) :=
  [(2, 100); (3, 200); (4, 400); (6, 800)].

(** the rank-rules never tier's ladder, the state census's own
    (Run_Compute.v [rank_rungs_census]) *)
Definition rank_rungs_tr : list (nat * nat) :=
  [(3, 0); (3, 64); (3, 256); (3, 1024)].

Definition qhb_rungs_tr : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024)].

(** the lex ladder is the expensive one (per rung: re-grow, explore,
    certificate search per instruction), and a failing machine pays
    every rung -- so it gets the single deepest horizon per window,
    and no n >= 5 rungs in-walk (context mixing at n <= 4 costs ~3/36
    pilot catches; those go to offline boards, PLAYBOOK Rule 4) *)
Definition qhb_lex_rungs_tr : list (nat * nat) :=
  [(2, 1024); (3, 1024); (4, 1024)].

(** the wrapped-RepWL tier's (L, T, t) ladder (Tier W-wrap,
    SCOPING_INSTR.md 7.1m): one rung -- it closed and passed every
    liveness gate on 81.8% of the measured suspects, and each rung a
    failing machine pays re-grows a full wrapped closure *)
Definition rw_qhb_rungs_tr : list (nat * nat * nat) :=
  [(2, 3, 1024)].

(** the RepWL tier's parameters, the state census's own
    (Run_Compute.v [rw_rungs_census] / [rw_fuel_census] /
    [rw_cut_census]) *)
Definition rw_rungs_tr : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].
Definition rw_fuel_tr : nat := 5120.
Definition rw_cut_tr : nat := 32.

Definition decider_tr : QHDecider :=
  decide_easy_tr B_tr 130 512 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_qhb_rungs_tr
    rw_rungs_tr rw_fuel_tr rw_cut_tr
    (dmap_of prov_tr_data) (dmap_of provqh_tr_data) (dmap_of D_tr).

(** ** The root and its symmetrized first level (Run_Compute.v shapes) *)

Definition TM0 : TM := fun _ _ => None.

Definition root : TNF_Node := mkNode TM0 (Some StB).

Definition child (w : Sym) (d : Dir) (nx : St) : TNF_Node :=
  mkNode (TM_upd' TM0 StA S0 (Some (mkTrans w d nx)))
         (ptr_after (Some StB) nx).

Definition q_0_tr : SearchQueue :=
  ([child S0 DR StA; child S1 DR StA; child S0 DR StB; child S1 DR StB],
   []).

Definition q_suc_tr (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_tr 13.

(** ** The FRONTIER decider: expansion only, no deciding

    The frontier prefix walk exists to produce a set of pending nodes
    to shard, and nothing else.  Running the full ladder there is pure
    waste, and it is the expensive kind: [node_expand h s i] takes the
    hole from [R_Halt s i], so EXPANSION only ever needs [find_halt] --
    the cheapest tier.  A node [find_halt] cannot place is a node that
    cannot be expanded, so the seconds the deep tiers spend on it buy
    the prefix nothing.  (Measured 2026-08-23: ~10 s per pop with the
    full decider, i.e. minutes to produce a frontier of a few hundred.)

    So the prefix uses halt-or-defer.  Nodes it cannot expand go
    straight to the back queue -- correct, just decided by a weaker
    tier than they would have been.  That costs at most a handful of
    extra rows in the collected list (the prefix pops ~13 per round),
    and it buys a frontier that is effectively free and can therefore
    be taken DEEP: more, smaller nodes, which is what makes the shards
    balance.

    Still well-formed: [R_Halt] is justified by [find_halt_sound]
    exactly as in [decide_easy_tr], and [R_Unknown] is trivially so. *)

Definition decider_tr_fast : QHDecider := fun tm =>
  match find_halt tm 130 0 c0 with
  | Some (n, s, i) => if S n <=? B_tr then R_Halt s i else R_Unknown
  | None => R_Unknown
  end.

Definition q_suc_tr_fast (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_tr_fast 13.

(** ** Balanced frontier expansion (untrusted sharding helper)

    [SearchQueue_upd] pushes a node's children at the FRONT of the
    front queue, so iterating it is a depth-first walk and the tail of
    the front queue is never touched.  That makes the front queue a
    bad thing to shard on: measured 2026-08-24, after 32 halt-only
    pops the 48-node frontier still had [child S1 DR StB] -- the
    unexpanded [1RB---_------_------_------] root child, a full
    quarter of the TNF tree -- sitting at index 47.  Its shard ran
    ~17 CPU-hours while the other 47 finished in minutes.

    [SearchQueue_level] instead expands EVERY node of the front queue
    exactly once, so the frontier is a genuine tree level and the
    shards are comparable in size.  Node order is preserved: children
    of an earlier node come before children of a later one.

    Untrusted, like all of the collection-mode serialization below:
    the split only decides how work is divided between processes, and
    the deferred list it feeds is re-derived by the eventual re-walk. *)
Definition SearchQueue_level (f : QHDecider) (q : SearchQueue) : SearchQueue :=
  fold_right
    (fun h acc =>
       match f (node_tm h) with
       | R_Halt s i => (node_expand h s i ++ fst acc, snd acc)
       | R_NeverQH | R_QH | R_Leaf | R_Deferred => acc
       | R_Unknown => (fst acc, h :: snd acc)
       end)
    ([], snd q) (fst q).

Definition SearchQueue_levels (f : QHDecider) (n : nat) (q : SearchQueue)
  : SearchQueue := Nat.iter n (SearchQueue_level f) q.

(** per-subtree roots, for splitting a long walk across processes *)
Definition q_sub_tr (w : Sym) (nx : St) : SearchQueue :=
  ([child w DR nx], []).
