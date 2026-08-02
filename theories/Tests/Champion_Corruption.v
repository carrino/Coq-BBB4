(** * Champion_Corruption: negative controls for the exact-score compute.

    BBB corruption-test tradition: the champion's exactness proof
    (Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v) rests on
    two binary-fuel [vm_compute] runs -- the landing at index 32,779,478
    (state [C], blank tape) and the last [StD] visit at index 32,779,477.
    Both index/state pairings must be RIGID: the same checks at the
    off-by-one index must fail.

    - at the landing itself the machine is in [StC], so the exactness
      witness ([StD]) is rejected there -- the lower bound cannot be
      inflated by one;
    - one step before the landing the machine is in [StD], so a claim
      that the terminal C-tail has already started is rejected -- the
      landing cannot be deflated by one.

    Each is one ~10 s [vm_compute]; a regression that made either pass
    would be a soundness alarm, not a convenience. *)

From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.
Import ListNotations.

(** At the landing (index 32,779,478) the state is [StC], not [StD]:
    claiming the exactness witness one step late is rejected. *)
Example champion_witness_not_at_landing :
  match cstepsN tm_champion champ_scoreN c0 with
  | Some c => st_eqb (fst c) StD
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** One step before the landing (index 32,779,477) the state is [StD],
    not [StC]: claiming the terminal C-tail one step early is
    rejected. *)
Example champion_tail_not_early :
  match cstepsN tm_champion champ_prevN c0 with
  | Some c => st_eqb (fst c) StC
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.
