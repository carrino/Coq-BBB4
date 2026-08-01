(** * 1RB0RB_1LC0RC_1RA0LD_0LB0LC -- three of four states, kernel-checked

    [ReachStI] certifies [StA], [StB] and [StC] live on this row.  The three
    lemmas below are the whole of that, re-checked by [vm_compute] inside
    each proof: nothing in [tools/reachsti/] carries weight, a wrong constant
    just makes [drop_ok] evaluate to [false].

    [StD] IS NOT HERE, AND IT IS NOT A SEARCH GAP.  It is permanently
    outside the [ReachStI] tier.  [drop_ok]'s measure is

        mu = B * ones l + C * ones r + rk (q, chd l, h, chd r)

    and it must strictly drop on every [StD]-avoiding step, but

        (StA,1,1,0) --A1=0RB--> (StB,0,0,0) --B0=1LC--> (StC,0,0,1)
                    --C0=1RA--> (StA,1,1,0)

    is a [StD]-avoiding cycle that returns [rk] to its start while [ones l]
    gains 1 and [ones r] is unchanged, so [mu] cannot drop around it for ANY
    [B, C >= 0].  Bellman-Ford is complete for each fixed [(B,C)], so the
    search really is exhaustive and not merely unlucky; it was pushed to
    [B,C <= 60] before the witness was extracted.  Method and the general
    form of the test: [docs/WAVE38_REST_FOUR.md] section 2b and the last
    section of [docs/REACHST_TIER.md].

    So this file is deliberately three lemmas and no theorem.  When [StD]
    falls to some other engine, [Checkers/LiveAll.neverqh_of_live4] closes
    the row in one line from these three plus that one. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From BBB4 Require Import BBB4_Statement CTape Checkers.ReachStI Checkers.LiveAll.

Definition tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StA) | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S0 DL StB) | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC : list St := [StA; StB; StC; StD].

Definition rkA_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 4
  | (StA, S0, S0, S1) => 4
  | (StA, S0, S1, S0) => 4
  | (StA, S0, S1, S1) => 4
  | (StA, S1, S0, S0) => 4
  | (StA, S1, S0, S1) => 4
  | (StA, S1, S1, S0) => 4
  | (StA, S1, S1, S1) => 4
  | (StB, S0, S0, S0) => 1
  | (StB, S0, S0, S1) => 4
  | (StB, S0, S1, S0) => 4
  | (StB, S0, S1, S1) => 4
  | (StB, S1, S0, S0) => 1
  | (StB, S1, S0, S1) => 4
  | (StB, S1, S1, S0) => 4
  | (StB, S1, S1, S1) => 4
  | (StC, S0, S0, S0) => 3
  | (StC, S0, S1, S0) => 3
  | (StC, S0, S1, S1) => 3
  | (StC, S1, S0, S0) => 3
  | (StC, S1, S1, S0) => 4
  | (StC, S1, S1, S1) => 3
  | (StD, S0, S0, S0) => 2
  | (StD, S0, S0, S1) => 4
  | (StD, S0, S1, S0) => 4
  | (StD, S0, S1, S1) => 4
  | (StD, S1, S0, S0) => 2
  | (StD, S1, S0, S1) => 4
  | (StD, S1, S1, S0) => 4
  | (StD, S1, S1, S1) => 4
  | _ => 0
  end.

Lemma liveA_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA 3 0 rkA_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.

Definition rkB_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 3
  | (StA, S0, S0, S1) => 3
  | (StA, S0, S1, S0) => 3
  | (StA, S0, S1, S1) => 3
  | (StA, S1, S1, S0) => 1
  | (StA, S1, S1, S1) => 1
  | (StB, S0, S0, S0) => 3
  | (StB, S0, S0, S1) => 3
  | (StB, S0, S1, S0) => 3
  | (StB, S0, S1, S1) => 3
  | (StB, S1, S0, S0) => 3
  | (StB, S1, S0, S1) => 3
  | (StB, S1, S1, S0) => 3
  | (StB, S1, S1, S1) => 3
  | (StC, S0, S0, S0) => 2
  | (StC, S0, S0, S1) => 3
  | (StC, S0, S1, S0) => 3
  | (StC, S0, S1, S1) => 3
  | (StC, S1, S0, S0) => 2
  | (StC, S1, S0, S1) => 3
  | (StC, S1, S1, S0) => 3
  | (StC, S1, S1, S1) => 3
  | (StD, S0, S0, S0) => 2
  | (StD, S0, S0, S1) => 3
  | (StD, S0, S1, S0) => 3
  | (StD, S0, S1, S1) => 3
  | (StD, S1, S0, S0) => 2
  | (StD, S1, S0, S1) => 3
  | (StD, S1, S1, S0) => 3
  | (StD, S1, S1, S1) => 3
  | _ => 0
  end.

Lemma liveB_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB 1 0 rkB_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.

Definition rkC_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 1
  | (StA, S0, S0, S1) => 1
  | (StA, S0, S1, S0) => 1
  | (StA, S0, S1, S1) => 1
  | (StA, S1, S0, S0) => 1
  | (StA, S1, S0, S1) => 1
  | (StA, S1, S1, S0) => 1
  | (StA, S1, S1, S1) => 1
  | (StC, S0, S0, S0) => 1
  | (StC, S0, S0, S1) => 1
  | (StC, S0, S1, S0) => 1
  | (StC, S0, S1, S1) => 1
  | (StC, S1, S0, S0) => 1
  | (StC, S1, S0, S1) => 1
  | (StC, S1, S1, S0) => 1
  | (StC, S1, S1, S1) => 1
  | (StD, S0, S0, S0) => 1
  | (StD, S0, S0, S1) => 1
  | (StD, S0, S1, S0) => 1
  | (StD, S0, S1, S1) => 1
  | (StD, S1, S0, S0) => 1
  | (StD, S1, S0, S1) => 1
  | (StD, S1, S1, S0) => 1
  | (StD, S1, S1, S1) => 1
  | _ => 0
  end.

Lemma liveC_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC 0 0 rkC_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.


(** The three, restated as [LiveSt] -- the shape [neverqh_of_live4] consumes. *)
Lemma liveStA_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA.
Proof. exact (live_of_recurs _ _ liveA_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

Lemma liveStB_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB.
Proof. exact (live_of_recurs _ _ liveB_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

Lemma liveStC_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC.
Proof. exact (live_of_recurs _ _ liveC_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

(** Any ONE of them already gives non-halting, with no [Visited] obligation. *)
Theorem nonhalt_1RB0RB_1LC0RC_1RA0LD_0LB0LC : NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC.
Proof. exact (nonhalt_of_live _ StA liveStA_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.
