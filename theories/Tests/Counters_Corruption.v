(** * Counters_Corruption: negative controls for the counter track.

    BBB corruption-test tradition: every computable ingredient of the
    counter proofs must REJECT mutated inputs.  The counter lap
    proofs rest on three kinds of checked computation --

    - windowed unit runs ([wsteps] closed by [reflexivity]): a wall
      that is too small, a wrong period, or a wrong claimed exit
      configuration must fail;
    - machine identity: a one-transition mutant of #10 must break
      the unit runs that exercise that transition;
    - the bootstrap anchor ([ceqb] against [Cc]): a wrong anchor
      index must be rejected.

    Everything here is decided by [vm_compute]/[discriminate]; a
    regression that made any of these pass would be a soundness
    alarm, not a convenience. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Machines.Counters Require Import Mono_10.
Import ListNotations.

(** ** Wall discipline: runs that need cells beyond the window fail *)

(** U5 (the left-edge turnaround) steps onto blank cells left of the
    wall: with the left wall ON it must die, not fabricate blanks. *)
Example wall_U5_left : wsteps true true tm_10 7 (StC, ([S1; S0; S1], S1, []))
                       = None.
Proof. reflexivity. Qed.

(** U9 (the overflow carry stop) runs off the right end: with the
    right wall ON it must die. *)
Example wall_U9_right : wsteps true true tm_10 5 (StB, ([], S1, []))
                        = None.
Proof. reflexivity. Qed.

(** U11 pops one cell of the left window; an empty left window dies. *)
Example wall_U11_left : wsteps true true tm_10 7 (StB, ([], S1, [S0; S0]))
                        = None.
Proof. reflexivity. Qed.

(** ** Unit-run mutations: wrong period or wrong exit are rejected *)

(** The comb crossing takes exactly 5 steps: at period 4 the run is
    mid-cycle, not back at a boundary in state B. *)
Example U2_wrong_period :
  wsteps true true tm_10 4 (StB, ([], S1, [S1; S0; S1]))
  <> Some (StB, ([S1; S1; S0], S1, [])).
Proof. discriminate. Qed.

(** The crossing deposits 011 (nearest-first 110), not 101. *)
Example U2_wrong_exit :
  wsteps true true tm_10 5 (StB, ([], S1, [S1; S0; S1]))
  <> Some (StB, ([S1; S0; S1], S1, [])).
Proof. discriminate. Qed.

(** The carry cycle flips the bit it consumes: claiming it preserves
    the pair is rejected. *)
Example U6_wrong_exit :
  wsteps true true tm_10 4 (StB, ([], S1, [S0; S1]))
  <> Some (StB, ([S0; S1], S1, [])).
Proof. discriminate. Qed.

(** ** Machine mutations break the units that fire the changed rule *)

(** #10 with D1 -> 1LB instead of 1LC (the prototype's falsify
    control "mutant D1"): the leftward comb crossing uses D1. *)
Definition tm_10_mutD1 : TM := fun q s =>
  match q, s with
  | StD, S1 => mk S1 DL StB
  | _, _ => tm_10 q s
  end.

Example mutD1_breaks_U4 :
  wsteps true true tm_10_mutD1 5 (StC, ([S1; S0; S1], S1, []))
  <> Some (StC, ([], S1, [S1; S0; S1])).
Proof. discriminate. Qed.

(** #10 with A0 -> 1LB (the prototype's "mutant A0"): the rightward
    comb crossing fires A0 at its last step. *)
Definition tm_10_mutA0 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DL StB
  | _, _ => tm_10 q s
  end.

Example mutA0_breaks_U2 :
  wsteps true true tm_10_mutA0 5 (StB, ([], S1, [S1; S0; S1]))
  <> Some (StB, ([S1; S1; S0], S1, [])).
Proof. discriminate. Qed.

(** Both mutants also miss the bootstrap anchor. *)
Example mutD1_breaks_boot :
  match csteps tm_10_mutD1 101 c0 with
  | Some c => ceqb c (Cc 2)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor mutations *)

(** The 101-step bootstrap lands on C(2), not C(3). *)
Example boot_wrong_anchor :
  match csteps tm_10 101 c0 with
  | Some c => ceqb c (Cc 3)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** The anchor family is rigid: C(2) with a mutated comb cell is not
    padding-equal to the bootstrap configuration. *)
Example boot_wrong_comb :
  match csteps tm_10 101 c0 with
  | Some c => ceqb c (StC, ([], S1,
                            rep [S1; S1; S0] 1 ++ S1 :: S0 :: Wp 2))
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Carry-view sanity: the two shapes are mutually exclusive *)

(** 5 = 101b has an interior carry (one low 1, rest 2), not the
    overflow shape. *)
Example cview_5 : cview 5 = (1, Some 1%positive).
Proof. reflexivity. Qed.

Example cview_7_overflow : cview 7 = (3, None).
Proof. reflexivity. Qed.

(** The working-area decomposition rejects a wrong carry count:
    W(5) starts 01 (bit 0 set), not 00. *)
Example W5_not_carry0 : forall w, Wp 5 <> S0 :: S0 :: w.
Proof. intros w H. discriminate H. Qed.
