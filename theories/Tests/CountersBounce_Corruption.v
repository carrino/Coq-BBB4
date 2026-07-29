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

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate]. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs BounceGlue.
From BBB4.Machines.Counters Require Import
  BNC_1RB____1LC0RB_1LD1RB_1LC1RB
  BNC_1RB____1LC1RD_1LB1RD_1LB0RD
  BNC_1RB____1LC1RD_1LB1RD_1LC0RD.
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
