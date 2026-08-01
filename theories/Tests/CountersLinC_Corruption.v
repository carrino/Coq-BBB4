(** * CountersLinC_Corruption: negative controls for the LinCarry boards.

    BBB corruption-test tradition: every computable ingredient of a proof
    must REJECT mutated inputs.  The three linear-search-carry counters
    (1RB1LA_0LA1RC_0LD0RC_1LD0RB, 1RB0LD_0LC0RB_1LA1RC_0RC1LD and
    1RB1LA_1LC0RD_0RA0LC_0LA1RD) rest on three things, and each is
    controlled here:

    - the boot step count is EXACT.  The anchor is reached at that step
      and at neither neighbour, so a board that guessed the boot wrong
      would not compile.
    - the lap step count is EXACT, not "at least".  One step short of a
      lap is not the next anchor, and neither is one step long -- the
      family is a genuine [csteps ... = Some ...], with no slack for a
      miscount to hide in.
    - the lap is QUADRATIC in the carry length, which is the whole reason
      these rows are not chain-reachable.  The laps at carry 1 and 2 fix
      an affine prediction for carry 3; that prediction is REFUTED here
      (it is short by exactly 2, the second difference).  A regression
      that made the affine prediction pass would mean the round trips had
      collapsed into a single sweep, i.e. a different machine.

    Everything is decided by [vm_compute]/[reflexivity]; a mutation that
    made any of these pass would be a soundness alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape KpCounter LinCarry.
From BBB4.Machines.Counters Require Import
  LinC_1RB1LA_0LA1RC_0LD0RC_1LD0RB
  LinC_1RB0LD_0LC0RB_1LA1RC_0RC1LD
  LinC_1RB1LA_1LC0RD_0RA0LC_0LA1RD.
Import ListNotations.

(** The deep word the laps below are checked against; the lap lemmas are
    uniform in it, so any word will do. *)
Definition Wc : list Sym := [S0; S1].

(** ** The boot constants are exact *)

Example boot_lp_exact :
  match csteps tm_lp 1 c0 with Some c => ceqb c (PCf StB 1) | None => false end
  = true.
Proof. vm_compute; reflexivity. Qed.

Example boot_lp_not_0 :
  match csteps tm_lp 0 c0 with Some c => ceqb c (PCf StB 1) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_lp_not_2 :
  match csteps tm_lp 2 c0 with Some c => ceqb c (PCf StB 1) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_sp_exact :
  match csteps tm_sp 10 c0 with Some c => ceqb c (SCf StB 2) | None => false end
  = true.
Proof. vm_compute; reflexivity. Qed.

Example boot_sp_not_9 :
  match csteps tm_sp 9 c0 with Some c => ceqb c (SCf StB 2) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_sp_not_11 :
  match csteps tm_sp 11 c0 with Some c => ceqb c (SCf StB 2) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_mr_exact :
  match csteps tmm_mr 3 c0 with Some c => ceqb c (SCf StC 1) | None => false end
  = true.
Proof. vm_compute; reflexivity. Qed.

Example boot_mr_not_2 :
  match csteps tmm_mr 2 c0 with Some c => ceqb c (SCf StC 1) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

Example boot_mr_not_4 :
  match csteps tmm_mr 4 c0 with Some c => ceqb c (SCf StC 1) | None => false end
  = false.
Proof. vm_compute; reflexivity. Qed.

(** The mirrored table really is the mirror: [mirror_ok_mr] is checked by
    the kernel in the board, and a table that differs in one cell is not. *)
Example mirror_mr_wrong :
  mirror_tm tm_mr StA S0 = Some (mkTrans S1 DR StB) -> False.
Proof. vm_compute. discriminate. Qed.

(** ** The laps are exact, and quadratic

    [tm_lp]: [(j+1)*(j+2)] = 6, 12, 20 at [j] = 1, 2, 3.
    [tm_sp] and [tmm_mr]: [j^2+3j+4] = 8, 14, 22. *)

Definition anc_lp (j : nat) : cconf := (StB, (rep [S1] j ++ S0 :: Wc, S0, [])).
Definition anc_lp' (j : nat) : cconf := (StB, (rep [S0] j ++ S1 :: Wc, S0, [])).

Example lap_lp_1 : csteps tm_lp 6 (anc_lp 1) = Some (anc_lp' 1).
Proof. vm_compute; reflexivity. Qed.

Example lap_lp_2 : csteps tm_lp 12 (anc_lp 2) = Some (anc_lp' 2).
Proof. vm_compute; reflexivity. Qed.

Example lap_lp_3 : csteps tm_lp 20 (anc_lp 3) = Some (anc_lp' 3).
Proof. vm_compute; reflexivity. Qed.

Example lap_lp_3_not_19 : csteps tm_lp 19 (anc_lp 3) = Some (anc_lp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

Example lap_lp_3_not_21 : csteps tm_lp 21 (anc_lp 3) = Some (anc_lp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

(** The affine prediction off the first two laps, 6 and 12, is 18. *)
Example lap_lp_3_not_affine :
  csteps tm_lp 18 (anc_lp 3) = Some (anc_lp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

Definition anc_sp (j : nat) : cconf :=
  (StB, (S0 :: rep [S1] j ++ S0 :: Wc, S0, [])).
Definition anc_sp' (j : nat) : cconf :=
  (StB, (S0 :: rep [S0] j ++ S1 :: Wc, S0, [])).

Example lap_sp_1 : csteps tm_sp 8 (anc_sp 1) = Some (anc_sp' 1).
Proof. vm_compute; reflexivity. Qed.

Example lap_sp_2 : csteps tm_sp 14 (anc_sp 2) = Some (anc_sp' 2).
Proof. vm_compute; reflexivity. Qed.

Example lap_sp_3 : csteps tm_sp 22 (anc_sp 3) = Some (anc_sp' 3).
Proof. vm_compute; reflexivity. Qed.

Example lap_sp_3_not_21 : csteps tm_sp 21 (anc_sp 3) = Some (anc_sp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

Example lap_sp_3_not_23 : csteps tm_sp 23 (anc_sp 3) = Some (anc_sp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

(** The affine prediction off 8 and 14 is 20. *)
Example lap_sp_3_not_affine :
  csteps tm_sp 20 (anc_sp 3) = Some (anc_sp' 3) -> False.
Proof. vm_compute. discriminate. Qed.

Definition anc_mr (j : nat) : cconf :=
  (StC, (S0 :: rep [S1] j ++ S0 :: Wc, S0, [])).
Definition anc_mr' (j : nat) : cconf :=
  (StC, (S0 :: rep [S0] j ++ S1 :: Wc, S0, [])).

Example lap_mr_3 : csteps tmm_mr 22 (anc_mr 3) = Some (anc_mr' 3).
Proof. vm_compute; reflexivity. Qed.

Example lap_mr_3_not_affine :
  csteps tmm_mr 20 (anc_mr 3) = Some (anc_mr' 3) -> False.
Proof. vm_compute. discriminate. Qed.

(** ** The spacer is load-bearing

    [tm_sp]'s counter is separated from the head by one blank cell.  Read
    WITHOUT that spacer -- the [Plain] anchor shape -- the same tape is
    not a lap of this machine at any of the three counts above. *)
Example sp_needs_spacer_8 :
  csteps tm_sp 8 (anc_lp 1) = Some (anc_lp' 1) -> False.
Proof. vm_compute. discriminate. Qed.

Example sp_needs_spacer_14 :
  csteps tm_sp 14 (anc_lp 2) = Some (anc_lp' 2) -> False.
Proof. vm_compute. discriminate. Qed.

Example sp_needs_spacer_22 :
  csteps tm_sp 22 (anc_lp 3) = Some (anc_lp' 3) -> False.
Proof. vm_compute. discriminate. Qed.
