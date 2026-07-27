(** * CountersWrapBc_Corruption: negative controls for the wrap bouncers.

    For 1RB---_1RC0RB_0LC0RD_1LD1LB and its mirror
    1RB---_1LC0LB_0RC0LD_1RD1RB we cover:

    - the quasihalting claim itself: [StA] must really be a dead end.
      Its S1 slot is undefined, and no transition of [StB]/[StC]/[StD]
      targets [StA] -- both facts are checked, and the second is what
      [closed_b] decides.  If either failed, the [QHBound 1] bound
      would be wrong, not merely unproven.
    - the boot constants (7 and 6) are exact, and off by one they fail.
    - the two doubling constants: the collapse is [3K+2] steps and one
      bounce is [2r+8].  Off-by-one in either is rejected.
    - the block sequence really doubles: 3 -> 7 -> 15, and 3 -> 14 (a
      plausible-looking wrong recurrence) is not reached.
    - a one-transition mutant that re-routes [StC] back into [StA]
      breaks closure, so the absorbing-set argument must reject it.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate]. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlueAbs WrapBouncer.
From BBB4.Machines.Counters Require Import WrapBc_R WrapBc_L.
Import ListNotations.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** StA is a dead end, in both senses *)

Example wr_A1_undefined : tm_wr StA S1 = None.
Proof. reflexivity. Qed.

Example wl_A1_undefined : tm_wl StA S1 = None.
Proof. reflexivity. Qed.

(** No transition out of {StB,StC,StD} targets StA -- this is exactly
    what makes [QuietFrom tm StA 1] true. *)
Example wr_core_closed : closed_b tm_wr [StB; StC; StD] = true.
Proof. vm_compute; reflexivity. Qed.

Example wl_core_closed : closed_b tm_wl [StB; StC; StD] = true.
Proof. vm_compute; reflexivity. Qed.

(** ...and the closure check is not vacuous: adding StA to a set whose
    only entry point is StA's own transition still leaves StA's
    undefined slot, so a set that omits StB is NOT closed. *)
Example wr_not_closed_without_B : closed_b tm_wr [StC; StD] = false.
Proof. vm_compute; reflexivity. Qed.

(** A mutant that sends StD back to StA breaks closure. *)
Definition tm_wr_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => None
  | StB, S0 => mkt S1 DR StC | StB, S1 => mkt S0 DR StB
  | StC, S0 => mkt S0 DL StC | StC, S1 => mkt S0 DR StD
  | StD, S0 => mkt S1 DL StD | StD, S1 => mkt S1 DL StA
  end.

Example mut_not_closed : closed_b tm_wr_mut [StB; StC; StD] = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The boot constants are exact *)

Example wr_boot_7 :
  match csteps tm_wr 7 c0 with
  | Some c => ceqb c (WrapBouncer.Cw WrapBc_R.mkA 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example wr_boot_not_6 :
  match csteps tm_wr 6 c0 with
  | Some c => ceqb c (WrapBouncer.Cw WrapBc_R.mkA 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example wl_boot_6 :
  match csteps tm_wl 6 c0 with
  | Some c => ceqb c (WrapBouncer.Cw WrapBc_L.mkA 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example wl_boot_not_7 :
  match csteps tm_wl 7 c0 with
  | Some c => ceqb c (WrapBouncer.Cw WrapBc_L.mkA 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The collapse is 3K+2, not 3K+1 or 3K+3 *)

Example wr_collapse_K7 :
  csteps tm_wr 23 (WrapBc_R.mkA 7) = Some (WrapBc_R.mkM 5 3).
Proof. vm_compute; reflexivity. Qed.

Example wr_collapse_not_22 :
  csteps tm_wr 22 (WrapBc_R.mkA 7) <> Some (WrapBc_R.mkM 5 3).
Proof. vm_compute. discriminate. Qed.

Example wr_collapse_not_24 :
  csteps tm_wr 24 (WrapBc_R.mkA 7) <> Some (WrapBc_R.mkM 5 3).
Proof. vm_compute. discriminate. Qed.

(** ** One bounce is 2r+8, and it moves 2 cells of wall into 4 of run *)

Example wr_bounce_5_3 :
  csteps tm_wr 14 (WrapBc_R.mkM 5 3) = Some (WrapBc_R.mkM 3 7).
Proof. vm_compute; reflexivity. Qed.

Example wr_bounce_not_13 :
  csteps tm_wr 13 (WrapBc_R.mkM 5 3) <> Some (WrapBc_R.mkM 3 7).
Proof. vm_compute. discriminate. Qed.

(** The wall must lose exactly 2 and the run gain exactly 4. *)
Example wr_bounce_not_1_7 :
  csteps tm_wr 14 (WrapBc_R.mkM 5 3) <> Some (WrapBc_R.mkM 1 7).
Proof. vm_compute. discriminate. Qed.

Example wr_bounce_not_3_6 :
  csteps tm_wr 14 (WrapBc_R.mkM 5 3) <> Some (WrapBc_R.mkM 3 6).
Proof. vm_compute. discriminate. Qed.

(** ** The block really doubles: 3 -> 7 -> 15 *)

(** K = 3: collapse 11 steps, then one terminal bounce 2*3+8 = 14. *)
Example wr_lap_3_to_7 :
  match csteps tm_wr 25 (WrapBc_R.mkA 3) with
  | Some c => ceqb c (WrapBc_R.mkA 7) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** K = 7: collapse 23, then bounces 14 + 22 + 30 = 66; total 89. *)
Example wr_lap_7_to_15 :
  match csteps tm_wr 89 (WrapBc_R.mkA 7) with
  | Some c => ceqb c (WrapBc_R.mkA 15) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** ...and not to 14 or 16: the recurrence is 2K+1, not 2K or 2K+2. *)
Example wr_lap_not_14 :
  match csteps tm_wr 89 (WrapBc_R.mkA 7) with
  | Some c => ceqb c (WrapBc_R.mkA 14) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example wr_lap_not_16 :
  match csteps tm_wr 89 (WrapBc_R.mkA 7) with
  | Some c => ceqb c (WrapBc_R.mkA 16) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example wl_lap_7_to_15 :
  match csteps tm_wl 89 (WrapBc_L.mkA 7) with
  | Some c => ceqb c (WrapBc_L.mkA 15) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** ** The block sequence is 2^(t+1) - 1 *)

Example bl_values : (bl 1, bl 2, bl 3, bl 4) = (3, 7, 15, 31).
Proof. vm_compute; reflexivity. Qed.
