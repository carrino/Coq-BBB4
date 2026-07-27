(** * CountersBnc3_Corruption: negative controls for the x3 bouncer.

    For 1RB1RA_0RC0RB_1LC1LD_0RA0LA the load-bearing claims are the two
    growth laws -- the wall moves one right and the block TRIPLES --
    and the fact that the bounce count is [m-1], i.e. determined by the
    anchor rather than searched for.  All three are checked here, along
    with the boot constant and the two per-round constants.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate]. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Machines.Counters Require Import Bnc3.
Import ListNotations.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** The boot constant is exact *)

Example boot_9 :
  match csteps tm_v4 9 c0 with
  | Some c => ceqb c (Cf 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example boot_not_8 :
  match csteps tm_v4 8 c0 with
  | Some c => ceqb c (Cf 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_not_10 :
  match csteps tm_v4 10 c0 with
  | Some c => ceqb c (Cf 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** One bounce is 6k+10, and it moves exactly one cell of block into
       three cells of zeros *)

Example round_k0 : csteps tm_v4 10 (mkB 2 5 0) = Some (mkB 2 4 1).
Proof. vm_compute; reflexivity. Qed.

Example round_k2 : csteps tm_v4 22 (mkB 2 5 2) = Some (mkB 2 4 3).
Proof. vm_compute; reflexivity. Qed.

Example round_k2_not_21 : csteps tm_v4 21 (mkB 2 5 2) <> Some (mkB 2 4 3).
Proof. vm_compute. discriminate. Qed.

(** The zero run grows by exactly 3 per bounce, not 2 or 4. *)
Example round_not_dz2 : csteps tm_v4 10 (mkB 2 5 0) <> Some (mkB 2 4 0).
Proof. vm_compute. discriminate. Qed.

Example round_block_drops_one : csteps tm_v4 10 (mkB 2 5 0) <> Some (mkB 2 3 1).
Proof. vm_compute. discriminate. Qed.

(** ** The wall turn is 6k+12 and moves the wall exactly one right *)

Example term_k2 : csteps tm_v4 24 (mkB 1 2 2) = Some (anc 2 9).
Proof. vm_compute; reflexivity. Qed.

Example term_k2_not_23 : csteps tm_v4 23 (mkB 1 2 2) <> Some (anc 2 9).
Proof. vm_compute. discriminate. Qed.

(** The wall must move one right, not stay. *)
Example term_wall_moves : csteps tm_v4 24 (mkB 1 2 2) <> Some (anc 1 9).
Proof. vm_compute. discriminate. Qed.

(** ** The block TRIPLES: 3 -> 9 -> 27, and the lap is 3m^2+7m+3 *)

(** m = 3: 3*9 + 21 + 3 = 51 steps. *)
Example lap_3_to_9 :
  match csteps tm_v4 51 (anc 0 3) with
  | Some c => ceqb c (anc 1 9) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example lap_3_not_doubling :
  match csteps tm_v4 51 (anc 0 3) with
  | Some c => ceqb c (anc 1 6) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example lap_3_not_quadrupling :
  match csteps tm_v4 51 (anc 0 3) with
  | Some c => ceqb c (anc 1 12) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** m = 9: 3*81 + 63 + 3 = 309 steps. *)
Example lap_9_to_27 :
  match csteps tm_v4 309 (anc 1 9) with
  | Some c => ceqb c (anc 2 27) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example lap_9_not_308 :
  match csteps tm_v4 308 (anc 1 9) with
  | Some c => ceqb c (anc 2 27) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The block sequence is 3^(t+1) *)

Example blk_values : (blk 1, blk 2, blk 3, blk 4) = (3, 9, 27, 81).
Proof. vm_compute; reflexivity. Qed.

Example wid_values : (wid 1, wid 2, wid 3) = (0, 1, 2).
Proof. vm_compute; reflexivity. Qed.

(** ** Unit mutation: re-route StC on S1 away from StD

    That transition is the one that turns the head around at the block;
    without it the five-step turn [mid5] does not hold. *)
Definition tm_v4_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S1 DR StA
  | StB, S0 => mkt S0 DR StC | StB, S1 => mkt S0 DR StB
  | StC, S0 => mkt S1 DL StC | StC, S1 => mkt S1 DL StA
  | StD, S0 => mkt S0 DR StA | StD, S1 => mkt S0 DL StA
  end.

Example mut_breaks_mid5 :
  csteps tm_v4_mut 5 (StC, ([S1; S1; S1], S0, []))
  <> Some (StB, ([S1; S1], S1, [S1])).
Proof. vm_compute. discriminate. Qed.

Example genuine_mid5 :
  csteps tm_v4 5 (StC, ([S1; S1; S1], S0, []))
  = Some (StB, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.
