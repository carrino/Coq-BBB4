(** * Census/Census_Compute_Split: the census theorem, one subtree at
    a time.

    Enable after the per-subtree probes print (0, 0, []) -- see
    NEXT_SESSION.md "The big compute".  Each lemma's Qed replays its
    subtree's enumeration through the kernel's native conversion; the
    four can be split into separate files for parallel `make`.

    The 0RA/1RA subtrees are single leaves (the blank-tape spinner and
    the right runner); the 0RB/1RB subtrees carry the actual walk. *)

From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run Run_Split.
Import ListNotations.

Lemma sub_0RA_empty : Nat.iter 4 q_suc (q_sub S0 StA) = ([], []).
Proof. native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)). Qed.

Lemma sub_1RA_empty : Nat.iter 4 q_suc (q_sub S1 StA) = ([], []).
Proof. native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)). Qed.

Lemma sub_0RB_empty : Nat.iter 700 q_suc (q_sub S0 StB) = ([], []).
Proof. native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)). Qed.

Lemma sub_1RB_empty : Nat.iter 700 q_suc (q_sub S1 StB) = ([], []).
Proof. native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)). Qed.

(** The census: every 4-state 2-symbol Turing machine either has all
    its BBB scores (last visits of eventually-quiet states) below
    [B_census] = 2000, or lies in the swap/mirror/completion orbit of
    the explicit deferred list (the 3,713 BBB(4) holdouts plus the
    measured hard residue of the generic tiers). *)
Theorem census_decided :
  forall tm, QHBound B_census tm \/ Deferred D_census tm.
Proof.
  apply census_from_subtrees.
  - exact (sub_decided S0 StA 4 eq_refl sub_0RA_empty).
  - exact (sub_decided S1 StA 4 eq_refl sub_1RA_empty).
  - exact (sub_decided S0 StB 700 eq_refl sub_0RB_empty).
  - exact (sub_decided S1 StB 700 eq_refl sub_1RB_empty).
Qed.

Print Assumptions census_decided.
