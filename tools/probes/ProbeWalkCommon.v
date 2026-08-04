(** Walk probe common defs: replicate Run.v's decider + the heavy
    GGH_0RB_1LC_0LB subtree root, with generated lookup tables standing
    in for the proven/provenqh maps (real D_census deferred map). *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs Deferred_Data.
From BBB4.Checkers Require Import Cycle TCycler NGram.
From BBB4 Require Import ProbeLookup.
Import ListNotations.

Definition Bc : nat := 2000.
Definition ngr : list (nat * nat) := [(2,100);(3,200);(4,400);(6,800)].
Definition rkr : list (nat * nat) := [(3,0);(3,64);(3,256);(3,1024)].
Definition qhr : list (nat * nat) :=
  [(2,64);(2,256);(2,1024);(3,64);(3,256);(3,1024);(4,64);(4,256);(4,1024)].
Definition rwr : list (nat * nat * nat) := [(2,2,0);(3,2,0);(4,2,0);(2,3,0)].

Definition pmap0 : DeferredMap := dmap_of probe_lookup.
Definition emap : DeferredMap := dmap_of [].
Definition dmap0 : DeferredMap := dmap_of D_census.

Definition decider0 : TM -> QHResult :=
  decide_easy Bc 130 512 200000 512 ngr rkr qhr rwr 8192 pmap0 emap dmap0.

Definition qsuc (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider0 13.

Definition TM0 : TM := fun _ _ => None.

(* the heavy unit GG_1LC_1LB: A0=1RB, B0=1LC, fill StC S1 := 1LB
   (exact replica of Run_Split2.tm_gg / ggchild S1 DL StB) *)
Definition tm_g : TM :=
  TM_upd' (TM_upd' TM0 StA S0 (Some (mkTrans S1 DR StB)))
          StB S0 (Some (mkTrans S1 DL StC)).
Definition gg_1LB : TNF_Node :=
  mkNode (TM_upd' tm_g StC S1 (Some (mkTrans S1 DL StB)))
         (ptr_after (Some StD) StB).
Definition q_probe : SearchQueue := ([gg_1LB], []).
