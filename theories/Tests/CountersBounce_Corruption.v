(** * CountersBounce_Corruption: negative controls for the erase/fill bouncers.

    The three [1RB---] rows of the residue's `no anchor` bucket, boarded by
    [Counters/BounceGlue.v] over the WALL-INDEXED family
    [mkB E j = (E, (repeat S0 j ++ [S1], S0, []))].  Covered here:

    - the quasihalting claim itself: [StA] must really be a dead end.  Its
      [S1] slot is undefined and no transition of the live three targets
      it -- the second is what [closed_b] decides.  If either failed the
      [QHBound 1] bound would be WRONG, not merely unproven.
    - the boot constant (4 on all three) is exact, and off by one it fails.
    - the lap constant [2*i+5] is exact: one step short and one step long
      both miss, at two different wall indices.
    - the lap really moves the WALL BY ONE.  [mkB 3 -> mkB 4] holds and
      [mkB 3 -> mkB 5] -- a plausible-looking wrong recurrence, and the one
      a "doubling bouncer" prior would predict -- is not reached.
    - the wall index is not a counter word: the anchor at [j] and the
      anchor at [j+1] differ in ONE cell, so no digit alphabet reads them.
    - a one-transition mutant that re-routes the eraser back into [StA]
      breaks closure, so the absorbing-set argument must reject it.
    - and, for the WALL BOUNCE class, that the wall gives up exactly one
      cell per bounce while the run gains exactly three, that the three
      collapses differ only in the drift's steps-per-cell, and that the
      block TRIPLES rather than doubling.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate]. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs BounceGlue.
From BBB4.Machines.Counters Require Import
  BNC_1RB____1LC0RB_1LD1RB_1LC1RB
  BNC_1RB____1LC1RD_1LB1RD_1LB0RD
  BNC_1RB____1LC1RD_1LB1RD_1LC0RD
  BNC_0RB0LD_1LA1LC_0LD0LC_1RD1RB
  BNC_0RB0RB_1LA1LC_0LD0LC_1RD1RB
  BNC_0RB1LA_1LA1LC_0LD0LC_1RD1RB
  BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Import ListNotations.

Local Notation t1 := BNC_1RB____1LC0RB_1LD1RB_1LC1RB.tm_1RB____1LC0RB_1LD1RB_1LC1RB.
Local Notation t2 := BNC_1RB____1LC1RD_1LB1RD_1LB0RD.tm_1RB____1LC1RD_1LB1RD_1LB0RD.
Local Notation t3 := BNC_1RB____1LC1RD_1LB1RD_1LC0RD.tm_1RB____1LC1RD_1LB1RD_1LC0RD.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** StA is a dead end, in both senses *)

Example t1_A1_undefined : t1 StA S1 = None.
Proof. reflexivity. Qed.

Example t2_A1_undefined : t2 StA S1 = None.
Proof. reflexivity. Qed.

Example t3_A1_undefined : t3 StA S1 = None.
Proof. reflexivity. Qed.

(** The live three are closed.  Note the ROLE ASSIGNMENT differs between
    the first machine and the other two -- the eraser is [StB] on one and
    [StD] on the others -- and the closure does not care. *)
Example t1_core_closed : closed_b t1 [StB; StC; StD] = true.
Proof. vm_compute; reflexivity. Qed.

Example t2_core_closed : closed_b t2 [StD; StB; StC] = true.
Proof. vm_compute; reflexivity. Qed.

Example t3_core_closed : closed_b t3 [StD; StC; StB] = true.
Proof. vm_compute; reflexivity. Qed.

(** ...and the check is not vacuous: drop a live state and it fails. *)
Example t1_not_closed_without_C : closed_b t1 [StB; StD] = false.
Proof. vm_compute; reflexivity. Qed.

(** A mutant that sends the eraser back to StA breaks closure. *)
Definition tm_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => None
  | StB, S0 => mkt S1 DL StC | StB, S1 => mkt S0 DR StB
  | StC, S0 => mkt S1 DL StD | StC, S1 => mkt S1 DR StB
  | StD, S0 => mkt S1 DL StC | StD, S1 => mkt S1 DR StA
  end.

Example mut_not_closed : closed_b tm_mut [StB; StC; StD] = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The boot constant is exact *)

Example t1_boot_4 :
  match csteps t1 4 c0 with
  | Some c => ceqb c (Cb StB 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example t1_boot_not_3 :
  match csteps t1 3 c0 with
  | Some c => ceqb c (Cb StB 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example t1_boot_not_5 :
  match csteps t1 5 c0 with
  | Some c => ceqb c (Cb StB 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example t2_boot_4 :
  match csteps t2 4 c0 with
  | Some c => ceqb c (Cb StD 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example t3_boot_4 :
  match csteps t3 4 c0 with
  | Some c => ceqb c (Cb StD 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** ** The lap constant 2*i+5 is exact, at two wall indices *)

(** i = 3: 11 steps, and neither 10 nor 12. *)
Example t1_lap_11 : csteps t1 11 (mkB StB 4) = Some (mkB StB 5).
Proof. vm_compute; reflexivity. Qed.

Example t1_lap_not_10 : csteps t1 10 (mkB StB 4) <> Some (mkB StB 5).
Proof. vm_compute; discriminate. Qed.

Example t1_lap_not_12 : csteps t1 12 (mkB StB 4) <> Some (mkB StB 5).
Proof. vm_compute; discriminate. Qed.

(** i = 7: 19 steps. *)
Example t1_lap_19 : csteps t1 19 (mkB StB 8) = Some (mkB StB 9).
Proof. vm_compute; reflexivity. Qed.

Example t2_lap_11 : csteps t2 11 (mkB StD 4) = Some (mkB StD 5).
Proof. vm_compute; reflexivity. Qed.

Example t3_lap_11 : csteps t3 11 (mkB StD 4) = Some (mkB StD 5).
Proof. vm_compute; reflexivity. Qed.

(** ** The wall moves by ONE, not by a doubling *)

(** The prior this bucket inherits from [WrapBouncer] is a DOUBLING
    bouncer.  These machines are not that: the lap lands on [mkB 5], and
    it does not land on [mkB 9] at any of the plausible costs. *)
Example t1_wall_not_double : csteps t1 11 (mkB StB 4) <> Some (mkB StB 9).
Proof. vm_compute; discriminate. Qed.

Example t1_two_laps : csteps t1 24 (mkB StB 4) = Some (mkB StB 6).
Proof. vm_compute; reflexivity. Qed.

(** ** The family is not a digit word

    Consecutive anchors differ by ONE blank cell, so no digit alphabet
    (whose unit is a whole digit) can read this family -- which is why
    eight waves of anchor enumeration returned nothing here. *)
Example anchors_differ_by_one_blank :
  mkB StB 5 = (StB, (S0 :: repeat S0 4 ++ [S1], S0, [])).
Proof. reflexivity. Qed.

(** ** The three theorems are the R_QH triple, on the real machines *)

Example t1_triple : NonHalt t1 /\ QHBound 2000 t1 /\ QuasiHaltsSt t1.
Proof. exact iqh_1RB____1LC0RB_1LD1RB_1LC1RB. Qed.

Example t2_triple : NonHalt t2 /\ QHBound 2000 t2 /\ QuasiHaltsSt t2.
Proof. exact iqh_1RB____1LC1RD_1LB1RD_1LB0RD. Qed.

Example t3_triple : NonHalt t3 /\ QHBound 2000 t3 /\ QuasiHaltsSt t3.
Proof. exact iqh_1RB____1LC1RD_1LB1RD_1LC0RD. Qed.

(** ** The WALL BOUNCE class: three machines that differ only in row A

    0RB0LD / 0RB0RB / 0RB1LA _1LA1LC_0LD0LC_1RD1RB.  Rows B, C and D are
    identical, so [BounceGlue.WallBounce] proves the bounce once and each
    board differs only in its collapse -- 3, 5 and 1 steps per cell
    of drift.  The controls below pin the parts a wrong reading would get
    wrong. *)

Local Notation u1 := BNC_0RB0LD_1LA1LC_0LD0LC_1RD1RB.tm_0RB0LD_1LA1LC_0LD0LC_1RD1RB.
Local Notation u2 := BNC_0RB0RB_1LA1LC_0LD0LC_1RD1RB.tm_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
Local Notation u3 := BNC_0RB1LA_1LA1LC_0LD0LC_1RD1RB.tm_0RB1LA_1LA1LC_0LD0LC_1RD1RB.

(** The bounce cost is [2*r+5] exactly, and the wall gives up exactly one
    cell while the run gains exactly three. *)
Example u1_bounce_11 : csteps u1 11 (wM StB 5 3) = Some (wM StB 4 6).
Proof. vm_compute; reflexivity. Qed.

Example u1_bounce_not_10 : csteps u1 10 (wM StB 5 3) <> Some (wM StB 4 6).
Proof. vm_compute; discriminate. Qed.

Example u1_bounce_not_12 : csteps u1 12 (wM StB 5 3) <> Some (wM StB 4 6).
Proof. vm_compute; discriminate. Qed.

(** The wall gives up ONE, not two: [wM 3 6] is not where the bounce lands. *)
Example u1_wall_one : csteps u1 11 (wM StB 5 3) <> Some (wM StB 3 6).
Proof. vm_compute; discriminate. Qed.

(** The run gains THREE, not two or four. *)
Example u1_run_three : csteps u1 11 (wM StB 5 3) <> Some (wM StB 4 5).
Proof. vm_compute; discriminate. Qed.

(** The terminal is the same chain read at [a = 0]. *)
Example u1_term : csteps u1 11 (wM StB 0 3) = Some (wA StB 6).
Proof. vm_compute; reflexivity. Qed.

(** The three collapses, one per drift speed: 3n+2, 5n+2 and n+7. *)
Example u1_collapse : csteps u1 (3 * 9 + 2) (wA StB 9) = Some (wM StB 7 3).
Proof. vm_compute; reflexivity. Qed.

Example u2_collapse : csteps u2 (5 * 9 + 2) (wA StB 9) = Some (wM StB 7 3).
Proof. vm_compute; reflexivity. Qed.

(** 0RB1LA's drift eats ONE cell fewer, so its collapse lands at [n-1]. *)
Example u3_collapse : csteps u3 (9 + 7) (wA StB 9) = Some (wM StB 8 3).
Proof. vm_compute; reflexivity. Qed.

Example u3_not_n2 : csteps u3 (9 + 7) (wA StB 9) <> Some (wM StB 7 3).
Proof. vm_compute; discriminate. Qed.

(** The macro law: the block TRIPLES on the first two and triples-plus-three
    on the third.  A doubling -- the WrapBouncer prior -- is refuted. *)
Example u1_macro : csteps u1 285 (wA StB 9) = Some (wA StB 27).
Proof. vm_compute; reflexivity. Qed.

Example u1_macro_not_double : csteps u1 285 (wA StB 9) <> Some (wA StB 18).
Proof. vm_compute; discriminate. Qed.

Example u3_macro : csteps u3 547 (wA StB 12) = Some (wA StB 39).
Proof. vm_compute; reflexivity. Qed.

(** All four states fire inside one lap, which is why these three close with
    [glue_neverqh] and not with a quasihalting tier. *)
Example u1_never : NeverQuasiHaltsSt u1.
Proof. exact BNC_0RB0LD_1LA1LC_0LD0LC_1RD1RB.nqh_0RB0LD_1LA1LC_0LD0LC_1RD1RB. Qed.

Example u2_never : NeverQuasiHaltsSt u2.
Proof. exact BNC_0RB0RB_1LA1LC_0LD0LC_1RD1RB.nqh_0RB0RB_1LA1LC_0LD0LC_1RD1RB. Qed.

Example u3_never : NeverQuasiHaltsSt u3.
Proof. exact BNC_0RB1LA_1LA1LC_0LD0LC_1RD1RB.nqh_0RB1LA_1LA1LC_0LD0LC_1RD1RB. Qed.

(** ** The MIRRORED wall bouncer: 0RB1RC_1RC0LB_0RD0RC_1LD1LA

    Same bounce, block on the right, and one measured difference: its drift
    walks the block with the head on a BLANK, because the wall turn writes
    [S0] rather than [S1].  The controls pin both halves of that. *)

Local Notation v0 :=
  BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA.tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Local Notation vm :=
  BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA.tmm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.

(** The mirror is the mirror -- the transfer rests on this and nothing else. *)
Example v_mirror_ok : mirror_tm v0 = vm.
Proof. exact BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA.mirror_ok_0RB1RC_1RC0LB_0RD0RC_1LD1LA. Qed.

(** THE discriminator: this machine's wall turn writes S0, u1's writes S1.
    That single cell is why it needs the second board template. *)
Example v_turn_writes_S0 : vm StA S0 = Some (mkTrans S0 DL StB).
Proof. reflexivity. Qed.

Example u1_turn_writes_S1 : u1 StB S0 = Some (mkTrans S1 DL StA).
Proof. reflexivity. Qed.

(** ...so its drift keeps the head on a BLANK and steps 5 cells at a time. *)
Example v_ripple_5 : csteps vm 5 (StA, ([S1; S1; S1], S0, [])) =
  Some (StA, ([S1; S1], S0, [S1])).
Proof. vm_compute; reflexivity. Qed.

Example v_ripple_not_4 : csteps vm 4 (StA, ([S1; S1; S1], S0, [])) <>
  Some (StA, ([S1; S1], S0, [S1])).
Proof. vm_compute; discriminate. Qed.

(** The bounce is bit-for-bit the same as u1's -- WallBounce proves it once. *)
Example v_bounce_11 : csteps vm 11 (wM StA 5 3) = Some (wM StA 4 6).
Proof. vm_compute; reflexivity. Qed.

Example v_term : csteps vm 11 (wM StA 0 3) = Some (wA StA 6).
Proof. vm_compute; reflexivity. Qed.

(** The collapse is 5n+2, the same law as u2's, and the block TRIPLES. *)
Example v_collapse : csteps vm (5 * 9 + 2) (wA StA 9) = Some (wM StA 7 3).
Proof. vm_compute; reflexivity. Qed.

Example v_macro : csteps vm 303 (wA StA 9) = Some (wA StA 27).
Proof. vm_compute; reflexivity. Qed.

(** And the conclusion holds of the REAL machine, not the mirror. *)
Example v_never : NeverQuasiHaltsSt v0.
Proof. exact BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA.nqh_0RB1RC_1RC0LB_0RD0RC_1LD1LA. Qed.
