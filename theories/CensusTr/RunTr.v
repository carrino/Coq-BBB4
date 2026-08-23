(** * CensusTr/RunTr: the transition-level census walk wiring.

    The transition-level analogue of Census/Run.v + Run_Compute.v, in
    COLLECTION MODE: the three lookup tiers (proven / proven-QH /
    deferred) start EMPTY, so the walk decides the halt + cycle bulk
    and pushes everything else to the back queue.  The back queue of a
    completed collection walk IS the transition-level deferred set --
    it gets frozen into generated DeferredTr tables, this file's lists
    are regenerated, and the re-walk with the frozen list yields the
    census theorem, exactly the bootstrap the state census used.

    The walk computation ([SearchQueue], [Nat.iter], the [node_expand]
    tree) is the state census's own, reused by import; the decider is
    CensusTr/DecideTr.v's phase-0 stack.  Iterating [q_suc_tr] past
    queue exhaustion is a no-op ([SearchQueue_upds] returns the queue
    unchanged once the front list is empty), so a generous iteration
    count is safe for driver units.

    [census_tr_from_empty] states the conditional theorem now, with
    the empty deferred list: it becomes the real census theorem the
    moment a walk over the FROZEN regenerated list empties the queue. *)

From Coq Require Import Arith Lia Bool List NArith.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import TNF_QHTr DecideTr.
(* the kernel-checked transition-level Proven tier: the 97 v1
   IRules certificates that survive the per-instruction prefix
   gate (SCOPING_INSTR.md 7.2).  739 KB of boards, so this is
   Required directly -- the state census's data/certificate
   split (Proven_List.v vs Proven_Data.v) exists for its 2.65 GB
   of boards and buys nothing at this size. *)
From BBB4.Machines Require Import
  IRules_Batch_00 IRules_Batch_01 IRules_Batch_02 IRules_Batch_03
  IRules_Batch_04 IRules_Batch_05 IRules_Batch_06 IRules_Batch_07
  IRules_Batch_08 IRulesTr_Batch_01.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Parameters: collection mode *)

Definition B_tr : nat := 2000.

Definition D_tr : list TM := [].
Definition prov_tr : list TM :=
  [tm_1RB1RA_0LC0LD_0RB1LC_1RA1LD;
   tm_1RB1LA_1LC1LD_1RC0RA_0LC0LD;
   tm_1RB0LA_1LCXXX_0LD0LC_1RD0RA;
   tm_1RB1LA_1LC1LC_0LD0LC_1RD0RA;
   tm_1RBXXX_1LC0LA_0LD0LC_1RD0RB;
   tm_1RB0LC_1LC1LA_0LD0LC_1RD0RB;
   tm_1RB1LA_1RC1RB_1LD0LA_0LA1LD;
   tm_1RB1LA_1RC1RB_0LD0LA_1LB1LD;
   tm_1RB1LA_1RC1RB_0LD0LA_0RC1LD;
   tm_1RB0LB_1RC1RB_1LD0RC_1LD1LA;
   tm_1RB1RC_1RC1RB_1LD0RC_1LD1LA;
   tm_1RB1RC_1LA1RB_1LD0RC_1LD1LA;
   tm_1RB0RD_1RC1RB_1LA1LC_1LC1RD;
   tm_1RB1RD_1RC1RB_1LC1LA_0RC0RD;
   tm_1RB1RD_1RC1RB_1LC1LA_1LC0RD;
   tm_1RB1RA_1LC1LB_0RA0RD_1LB1RD;
   tm_1RB1RD_0LC1RC_1LC1LA_1LB0RD;
   tm_1RB1RA_1LC1LB_1RA0RD_1LB1RD;
   tm_1RB1RA_1LC0LD_0LD1LC_1RA1LD;
   tm_1RB1RA_0LC0LD_0LD1LC_1RA1LD;
   tm_1RB1RD_0LC1RB_1LC1LA_0RB0RD;
   tm_1RB1RD_0LC1RB_1LC1LA_0RC0RD;
   tm_1RB1RD_0LC1RB_1LC1LA_1LC0RD;
   tm_1RB1RC_0LA1RB_1LD0RC_1LD1LA;
   tm_1RB1LA_1RC1RB_0LD0LA_0LA1LD;
   tm_1RB1LA_1RC1RB_1LD0LA_1LB1LD;
   tm_1RB0LA_1LB0LC_0LD0LC_1RD0RA;
   tm_1RB1LA_1LA0LC_1RD1LC_1RB1RD;
   tm_1RB1RA_1LC0LD_1RB1LC_1RA1LD;
   tm_1RB1RA_0LC0LD_1LA1LC_1RA1LD;
   tm_1RB1LA_1RC1RB_1LD0LA_1RC1LD;
   tm_1RB1LA_1LA1LC_0LD0LC_1RD1RB;
   tm_1RB1LA_1LA1LC_1RD0LC_1RD1RB;
   tm_1RB1RD_1LB0LC_1LA1RC_0RB0RD;
   tm_1RB1RA_1LC0RB_1LC1LD_0RA0LA;
   tm_1RB1RA_1LC0RB_1LC1LD_0RA1RB;
   tm_1RB1RD_0LC0RC_1LC1LA_0RB0RD;
   tm_1RB1LB_0LC0LB_0LD1LC_1RD1RA;
   tm_1RB1RA_1LB1LC_0RA1RD_0RB0RD;
   tm_1RB1RA_1LB1LC_0RA1RD_1LB0RD;
   tm_1RB1RA_1LC0LD_0RB1LC_1RA1LD;
   tm_1RB1RC_0RC1RB_0RD0RC_1LD1LA;
   tm_1RB1RD_0RC0RB_1LC0LA_0RA1LB;
   tm_1RB1RD_0RC0RB_1LC0LA_1LA0RB;
   tm_1RB1RD_0RC0RB_1LC0LA_0RBXXX;
   tm_1RB1RD_0RC0RD_1LC0LA_0RB0RD;
   tm_1RB1LA_0LA1LC_0LD0LC_1RD1RB;
   tm_1RB1RD_0RC0RB_1LC0LA_0RD0RB;
   tm_1RB1LA_0LA1LC_1RD0LC_1RD1RB;
   tm_1RB1RD_0RC0RB_1LC0LA_1LD1RB;
   tm_1RB1RD_0RC0RB_1LC0LA_1RD1LB;
   tm_1RB1RA_1LC0RB_1LC1LD_1RA0LA;
   tm_1RB1RA_1LC0RB_1LC1LD_1RA1RB;
   tm_1RB1LB_0LC0LB_0RD1LC_1RD1RA;
   tm_1RB1RD_0RC1RB_1LC1LA_0LB0RD;
   tm_1RB1RD_0RC1RB_1LC1LA_0RB0RD;
   tm_1RB1RD_0RC1RB_1LC1LA_0RC0RD;
   tm_1RB1RC_1LA1RB_0RD0RC_1LD1LA;
   tm_1RB1RD_0RC1RB_1LC1LA_1LC0RD;
   tm_1RB1LA_1RC1RB_1LD0LA_0RC1LD;
   tm_1RB1LA_0LC0LB_1RC1RD_1LA1LB;
   tm_1RB1RD_1LC0RC_1LC1LA_0RB0RD;
   tm_1RB1RD_1LC0RC_1LC1LA_1LB0RD;
   tm_1RBXXX_0RC0RB_1LC0LD_1LA0RD;
   tm_1RB1RB_0RC0RB_1LC0LD_1LA1RD;
   tm_1RB1LA_0LA0LC_1RD1LC_1RB1RD;
   tm_1RB1RC_0RC1RB_1LD0RC_1LD1LA;
   tm_1RB1RA_1LC0LD_1LA1LC_1RA1LD;
   tm_1RB1RA_0RC0RB_1LC1LD_0RD0LA;
   tm_1RB0RD_0RC0RB_1LC0LA_1LAXXX;
   tm_1RB1RA_1LB1LC_1RA1RD_0RB0RD;
   tm_1RB1RA_1LB1LC_1RA1RD_1LB0RD;
   tm_1RB0LA_0RC0RB_1LC1LD_0RA1RB;
   tm_1RB1RA_0RC0RB_1LC1LD_0RA1RB;
   tm_1RB1RA_0RC1LD_1LC0LA_0LB0RD;
   tm_1RB0LB_1RC1RB_0RD0RC_1LD1LA;
   tm_1RB1RA_0RC1LD_1LC0LA_0RB0RD;
   tm_1RB1RA_0RC1LD_1LC0LA_0RC0RD;
   tm_1RB1RC_1RC1RB_0RD0RC_1LD1LA;
   tm_1RB1RA_0RC1LD_1LC0LA_1LC0RD;
   tm_1RB1RC_1RC0RD_0LB0RC_1LD1LA;
   tm_1RB0RC_0LA1RB_1LD1RC_1LA1LD;
   tm_1RB1LA_1RC1RB_0LD0LA_1RC1LD;
   tm_1RB1LB_0LC0LB_1RD1LC_1RD1RA;
   tm_1RB1RD_1LC1RB_1LC1LA_0RB0RD;
   tm_1RB1RA_0RC0RB_1LC1LD_1RA0LA;
   tm_1RB1RD_1LC1RB_1LC1LA_1LB0RD;
   tm_1RB1RD_1LC1RB_1LC1LA_0RC0RD;
   tm_1RB1RA_0RC0RB_1LC1LD_1RA1RB;
   tm_1RB1RD_1LC1RB_1LC1LA_1LC0RD;
   tm_1RB1RC_0LA1RB_0RD0RC_1LD1LA;
   tm_1RB1RA_0LC0LD_1RB1LC_1RA1LD;
   tm_1RB0RC_1LA1RB_1LD1RC_1LA1LD;
   tm_1RB1RD_0RC0RC_1LC1LA_0LB0RD;
   tm_1RB1RD_0RC0RC_1LC1LA_0RB0RD;
   tm_1RB0RC_0RC1RB_1LD1RC_1LA1LD;
   tm_1RB1RD_0LC1RD_1LC1LA_1LB0RD].
Definition provqh_tr : list TM := [].

Lemma prov_tr_all : Forall NeverQuasiHaltsTr prov_tr.
Proof.
  unfold prov_tr.
  apply Forall_cons; [exact irtr_1RB1RA_0LC0LD_0RB1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1LC1LD_1RC0RA_0LC0LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LA_1LCXXX_0LD0LC_1RD0RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1LC1LC_0LD0LC_1RD0RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RBXXX_1LC0LA_0LD0LC_1RD0RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LC_1LC1LA_0LD0LC_1RD0RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_1LD0LA_0LA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_0LD0LA_1LB1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_0LD0LA_0RC1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LB_1RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_1RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_1LA1RB_1LD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0RD_1RC1RB_1LA1LC_1LC1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1RC1RB_1LC1LA_0RC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1RC1RB_1LC1LA_1LC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC1LB_0RA0RD_1LB1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC1RC_1LC1LA_1LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC1LB_1RA0RD_1LB1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0LD_0LD1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0LC0LD_0LD1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC1RB_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC1RB_1LC1LA_0RC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC1RB_1LC1LA_1LC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_0LA1RB_1LD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_0LD0LA_0LA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_1LD0LA_1LB1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LA_1LB0LC_0LD0LC_1RD0RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1LA0LC_1RD1LC_1RB1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0LD_1RB1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0LC0LD_1LA1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_1LD0LA_1RC1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1LA1LC_0LD0LC_1RD1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1LA1LC_1RD0LC_1RD1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LB0LC_1LA1RC_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0RB_1LC1LD_0RA0LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0RB_1LC1LD_0RA1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC0RC_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LB_0LC0LB_0LD1LC_1RD1RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LB1LC_0RA1RD_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LB1LC_0RA1RD_1LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0LD_0RB1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_0RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_0RA1LB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_1LA0RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_0RBXXX_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RD_1LC0LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_0LA1LC_0LD0LC_1RD1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_0RD0RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_0LA1LC_1RD0LC_1RD1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_1LD1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RB_1LC0LA_1RD1LB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0RB_1LC1LD_1RA0LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0RB_1LC1LD_1RA1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LB_0LC0LB_0RD1LC_1RD1RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC1RB_1LC1LA_0LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC1RB_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC1RB_1LC1LA_0RC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_1LA1RB_0RD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC1RB_1LC1LA_1LC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_1LD0LA_0RC1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_0LC0LB_1RC1RD_1LA1LB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC0RC_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC0RC_1LC1LA_1LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RBXXX_0RC0RB_1LC0LD_1LA0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RB_0RC0RB_1LC0LD_1LA1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_0LA0LC_1RD1LC_1RB1RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_0RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LC0LD_1LA1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC0RB_1LC1LD_0RD0LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0RD_0RC0RB_1LC0LA_1LAXXX_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LB1LC_1RA1RD_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_1LB1LC_1RA1RD_1LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LA_0RC0RB_1LC1LD_0RA1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC0RB_1LC1LD_0RA1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC1LD_1LC0LA_0LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0LB_1RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC1LD_1LC0LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC1LD_1LC0LA_0RC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_1RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC1LD_1LC0LA_1LC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_1RC0RD_0LB0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0RC_0LA1RB_1LD1RC_1LA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LA_1RC1RB_0LD0LA_1RC1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1LB_0LC0LB_1RD1LC_1RD1RA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC1RB_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC0RB_1LC1LD_1RA0LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC1RB_1LC1LA_1LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC1RB_1LC1LA_0RC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0RC0RB_1LC1LD_1RA1RB_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_1LC1RB_1LC1LA_1LC0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RC_0LA1RB_0RD0RC_1LD1LA_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RA_0LC0LD_1RB1LC_1RA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0RC_1LA1RB_1LD1RC_1LA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RC_1LC1LA_0LB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0RC0RC_1LC1LA_0RB0RD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB0RC_0RC1RB_1LD1RC_1LA1LD_never_quasihalts_tr|].
  apply Forall_cons; [exact irtr_1RB1RD_0LC1RD_1LC1LA_1LB0RD_never_quasihalts_tr|].
  apply Forall_nil.
Qed.

Lemma provqh_tr_all :
  Forall (fun tm => NonHalt tm /\ QHBoundTr B_tr tm /\ QuasiHaltsTr tm)
         provqh_tr.
Proof. constructor. Qed.

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

(** the RepWL tier's parameters, the state census's own
    (Run_Compute.v [rw_rungs_census] / [rw_fuel_census] /
    [rw_cut_census]) *)
Definition rw_rungs_tr : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].
Definition rw_fuel_tr : nat := 5120.
Definition rw_cut_tr : nat := 32.

Definition decider_tr : QHDecider :=
  decide_easy_tr B_tr 130 512 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_rungs_tr rw_fuel_tr rw_cut_tr
    (dmap_of prov_tr) (dmap_of provqh_tr) (dmap_of D_tr).

Lemma decider_tr_WF : QHDeciderTr_WF B_tr D_tr decider_tr.
Proof.
  exact (decide_easy_tr_WF B_tr D_tr 130 512 200000 512
           ng_rungs_tr rank_rungs_tr qhb_rungs_tr qhb_lex_rungs_tr
           rw_rungs_tr rw_fuel_tr rw_cut_tr
           prov_tr prov_tr_all provqh_tr provqh_tr_all).
Qed.

(** ** The ESCALATED (offline) configuration

    The walk's ladders are trimmed for WALK cost: every deferred-bound
    machine pays every rung it fails, at every node, so the walk gets
    the cheap end of each tier (SCOPING_INSTR.md section 7.1d).  The
    LIST-BURN has no such constraint -- it is per-machine and
    embarrassingly parallel over a fixed list -- so it runs the same
    tiers with 10-100x the fuel and the wide windows the walk cannot
    afford.  Same checkers, same soundness: only the parameter tuple
    differs, and [decide_easy_tr_WF] is parametric in it, so
    [decider_tr_deep] satisfies the SAME census contract at the SAME
    bound.

    Note the asymmetry, and why it is forced: the QH tiers conclude
    [QHBoundTr (S t)] and the pipeline guards them with [S t <=? B],
    so their prefix horizon cannot exceed [B_tr] -- escalating them
    means WIDER windows (n = 5, 6, 8), not deeper prefixes.  The NEVER
    tiers carry no bound, so they escalate in both directions.  Keeping
    [B_tr] fixed is what makes the burn's survivor count honest: a
    machine this decides is one a re-walk with these ladders would also
    decide. *)

Definition ng_rungs_deep : list (nat * nat) :=
  [(2, 100); (3, 200); (4, 400); (6, 800); (8, 1600); (10, 4096)].

Definition rank_rungs_deep : list (nat * nat) :=
  [(3, 0); (3, 64); (3, 256); (3, 1024);
   (4, 1024); (5, 1024); (6, 4096)].

Definition qhb_rungs_deep : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024);
   (5, 256); (5, 1024); (6, 1024); (8, 1024)].

Definition qhb_lex_rungs_deep : list (nat * nat) :=
  [(2, 1024); (3, 1024); (4, 1024); (5, 1024); (6, 1024)].

Definition rw_rungs_deep : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0);
   (5, 2, 0); (3, 3, 0); (4, 3, 0); (2, 4, 0)].

Definition rw_fuel_deep : nat := 40960.
Definition rw_cut_deep : nat := 128.

Definition decider_tr_deep : QHDecider :=
  decide_easy_tr B_tr 130 4096 1000000 2048 ng_rungs_deep rank_rungs_deep
    qhb_rungs_deep qhb_lex_rungs_deep rw_rungs_deep rw_fuel_deep rw_cut_deep
    (dmap_of prov_tr) (dmap_of provqh_tr) (dmap_of D_tr).

Lemma decider_tr_deep_WF : QHDeciderTr_WF B_tr D_tr decider_tr_deep.
Proof.
  exact (decide_easy_tr_WF B_tr D_tr 130 4096 1000000 2048
           ng_rungs_deep rank_rungs_deep qhb_rungs_deep qhb_lex_rungs_deep
           rw_rungs_deep rw_fuel_deep rw_cut_deep
           prov_tr prov_tr_all provqh_tr provqh_tr_all).
Qed.


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

Lemma decider_tr_fast_WF : QHDeciderTr_WF B_tr D_tr decider_tr_fast.
Proof.
  intro tm. unfold decider_tr_fast.
  destruct (find_halt tm 130 0 c0) as [[[n s] i]|] eqn:Eh; [|exact I].
  destruct (S n <=? B_tr) eqn:EB; [|exact I].
  apply Nat.leb_le in EB.
  destruct (find_halt_sound tm 130 0 c0 n s i (eq_refl) Eh)
    as (tp & Hst & Hhd & Hnone).
  exists n, tp. auto.
Qed.

Definition q_suc_tr_fast (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_tr_fast 13.

(** per-subtree roots, for splitting a long walk across processes *)
Definition q_sub_tr (w : Sym) (nx : St) : SearchQueue :=
  ([child w DR nx], []).

(** ** Well-formedness of the symmetrized root *)

Lemma root_WF : Node_WF root.
Proof.
  unfold Node_WF, root; simpl.
  intro u.
  split.
  - intros (_ & _ & HA). destruct u; simpl; congruence || lia.
  - intro Hu. repeat split.
    + intros q s tr H. discriminate.
    + intro Hc. subst u. simpl in Hu. lia.
Qed.

Lemma mirror_child : forall w d nx,
  mirror_tm (TM_upd' TM0 StA S0 (Some (mkTrans w d nx))) =
  TM_upd' TM0 StA S0 (Some (mkTrans w (mirror_dir d) nx)).
Proof.
  intros w d nx.
  rewrite !TM_upd'_spec.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  unfold mirror_tm, TM_upd, TM0.
  destruct (st_eqb q StA && sym_eqb s S0); reflexivity.
Qed.

Lemma child_WF : forall w d nx,
  trans_ok (Some StB) (mkTrans w d nx) = true ->
  Node_WF (child w d nx).
Proof.
  intros w d nx Hok.
  unfold Node_WF, child; simpl.
  rewrite TM_upd'_spec.
  apply (UnusedState_ptr_upd TM0 StA S0 (mkTrans w d nx) (Some StB)).
  - reflexivity.
  - intros (_ & _ & HA). congruence.
  - exact root_WF.
  - exact Hok.
Qed.

Lemma q_0_tr_WF : SearchQueue_WF_Tr B_tr D_tr q_0_tr root.
Proof.
  assert (Hhole : TM0 StA S0 = None) by reflexivity.
  assert (Hstep : stepn TM0 0 InitES = Some (StA, mkTape blank_side S0 blank_side))
    by reflexivity.
  assert (HB : 1 <= B_tr) by (unfold B_tr; lia).
  pose proof (node_expand_tr_spec B_tr D_tr TM0 (Some StB) 0 StA
                (mkTape blank_side S0 blank_side) Hstep Hhole HB
                (root_WF)) as [_ Hexp_dec].
  split.
  - intros x Hin.
    simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; apply child_WF; reflexivity.
  - intros Hd.
    change (NodeDecidedTr B_tr D_tr TM0).
    apply Hexp_dec.
    intros x' Hin.
    cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
         t_next t_head St_to_nat Nat.leb In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      cbn [node_tm].
    + (* S0 DL StA: mirror of child S0 DR StA *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S0 DL StA). cbn [mirror_dir].
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DL StB *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S0 DL StB). cbn [mirror_dir].
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S0 DR StA *)
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DR StB *)
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S1 DL StA *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S1 DL StA). cbn [mirror_dir].
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DL StB *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S1 DL StB). cbn [mirror_dir].
      apply (Hd (child S1 DR StB)). simpl; tauto.
    + (* S1 DR StA *)
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DR StB *)
      apply (Hd (child S1 DR StB)). simpl; tauto.
Qed.

Lemma q_iter_tr_WF : forall n,
  SearchQueue_WF_Tr B_tr D_tr (Nat.iter n q_suc_tr q_0_tr) root.
Proof.
  induction n.
  - exact q_0_tr_WF.
  - simpl.
    apply SearchQueue_upds_spec_tr; [exact IHn | exact decider_tr_WF].
Qed.

(** ** The theorem, conditional on the computation emptying the queue *)

Lemma census_tr_from_empty :
  forall n, Nat.iter n q_suc_tr q_0_tr = ([], []) ->
  forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm.
Proof.
  intros n Hempty tm.
  pose proof (q_iter_tr_WF n) as HWF.
  rewrite Hempty in HWF.
  pose proof (SearchQueue_empty_decided_tr B_tr D_tr root HWF) as Hnd.
  exact (Hnd tm (TM_le_TM0 (node_tm root) tm (fun _ _ => eq_refl))).
Qed.

(** ** Collection-walk output helpers (untrusted serialization)

    [queue_encs] renders the back queue -- the deferred candidates --
    as [tm_enc] codes, printed by Coq as decimal [N] literals; the
    untrusted tools/censustr/decode_enc.py turns them back into
    bbchallenge machine text and DeferredTr tables. *)

Definition tm_row (tm : TM) : list (option Trans) :=
  [tm StA S0; tm StA S1; tm StB S0; tm StB S1;
   tm StC S0; tm StC S1; tm StD S0; tm StD S1].

Definition queue_sizes (q : SearchQueue) : nat * nat :=
  (length (fst q), length (snd q)).

Definition queue_encs (q : SearchQueue) : list N :=
  map (fun x => N.pos (tm_enc (node_tm x))) (snd q).

(** front-queue serialization for the FRONTIER SPLIT (parallel
    collection): each pending node as (machine code, TNF pointer
    code), so tools/censustr/gen_walk_shards.py can partition the
    frontier across independent shard processes.  Untrusted, like all
    collection serialization: the re-walk re-derives everything. *)
Definition ptr_enc (p : option St) : N :=
  match p with
  | None => 0
  | Some StA => 1
  | Some StB => 2
  | Some StC => 3
  | Some StD => 4
  end%N.

Definition queue_front_encs (q : SearchQueue) : list (N * N) :=
  map (fun x => (N.pos (tm_enc (node_tm x)), ptr_enc (node_ptr x)))
      (fst q).
