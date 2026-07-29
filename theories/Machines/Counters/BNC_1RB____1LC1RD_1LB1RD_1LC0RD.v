(** * BNC_1RB____1LC1RD_1LB1RD_1LC0RD: machine 1RB---_1LC1RD_1LB1RD_1LC0RD quasihalts, with bound 1.

    One of the three [1RB---] rows of the residue's `no anchor` bucket.
    [StA]'s [S1] transition is undefined, so [StA] fires once -- at
    configuration index 0 -- and [StD], [StC], [StB] are CLOSED
    under the table: the machine genuinely QUASIHALTS and never halts, so
    the never-quasihalting tier can only reject it.  The tier it needs is
    [QHBound], via [LapGlueAbs.glue_qh_abs].

    The 3-state core is the ERASE/FILL bouncer of [BounceGlue], and the
    counter is THE WALL POSITION, not a word:

      mkB j = (StD, (repeat S0 j ++ [S1], S0, []))

    -- the head on the blank frontier, [j] erased cells behind it, and the
    surviving wall cell at the far end.  [StD] sweeps right over ones
    writing zeros; [StC] and [StB] sweep back left over the zeros
    writing ones, alternating; the wall turns them around.  One bounce is

      mkB (S i)  -->  mkB (S (S i))   in exactly  2*i+5  steps,

    so the wall moves by exactly one cell per cycle and the cost is affine
    in the wall index -- a PLAIN bouncer, no measure and no well-founded
    recursion.  This is why eight waves of digit-alphabet anchor search
    returned nothing on this row: there is no digit word to find.

    The whole design was measured off the raw simulator by
    [tools/counters/bouncecert.py] (turnaround columns, wall step, cycle
    cost law, and the wall-indexed turnaround families) and the lap
    differentially validated at [j = 1..59] before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs BounceGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB---_1LC1RD_1LB1RD_1LC0RD *)
Definition tm_1RB____1LC1RD_1LB1RD_1LC0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S0 DR StD end.

(** The wall-indexed anchor: [Cb StD p = mkB StD (Pos.to_nat p)]. *)
Lemma boot_1RB____1LC1RD_1LB1RD_1LC0RD : exists t0,
  stepn tm_1RB____1LC1RD_1LB1RD_1LC0RD t0 InitES = Some (lift (Cb StD 1)).
Proof.
  exists 4.
  assert (H : match csteps tm_1RB____1LC1RD_1LB1RD_1LC0RD 4 c0 with
              | Some c => ceqb c (Cb StD 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_1RB____1LC1RD_1LB1RD_1LC0RD 4 c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

(** 1RB---_1LC1RD_1LB1RD_1LC0RD: never halts, quasihalts, and every quiet state made its last
    visit by index 1. *)
Theorem iqh_1RB____1LC1RD_1LB1RD_1LC0RD : iqh tm_1RB____1LC1RD_1LB1RD_1LC0RD.
Proof.
  apply (bounce_qh tm_1RB____1LC1RD_1LB1RD_1LC0RD StD StC StB
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           boot_1RB____1LC1RD_1LB1RD_1LC0RD
           ltac:(vm_compute; reflexivity)
           ltac:(eexists; split; [vm_compute; reflexivity | cbn; tauto])
           ltac:(cbn; intuition discriminate)).
Qed.
