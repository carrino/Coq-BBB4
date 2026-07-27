(** * CountersW15_Corruption: negative controls for wave4 #15.

    BBB corruption-test tradition: every computable ingredient of the
    proof must REJECT mutated inputs.  For #15
    (1RB0RC_0LC1LB_0LD1LC_1RD0RA) the ingredients worth attacking are
    the ones that were nearly got wrong:

    - the DEPOSIT is a SWEEP, not a fixed window.  It passed a
      42-context sample and a naive "does the tail pass through" window
      search, and failed the exhaustive check on 496 of 961 contexts.
      Here both of its cases are pinned, and the naive one-window
      reading is shown false in the very context where it is tempting;
    - [btail]'s two branches -- interior deposit ([+2] here, [+1] on the
      next block) versus SPAWN at the top ([+1] here, then a new
      length-2 block).  Reading the spawn as a bare bump, or the
      interior case as a spawn, gives the wrong vector;
    - the scan stops at the first ODD block, not at the frontier: at
      [p = 7] the frontier block (8) is carried OVER;
    - every step count: the boot, the constant even lap, and five odd
      laps, each with its off-by-one rejected;
    - unit mutation: [B1 = 1LB] re-routed to [StC].  That is exactly the
      walk-back step of the deposit's sweep, so [dep2], [cross7] and
      [ruleA] die while [out6], [entry5], [carry5], [dep0], [ret1] and
      [exit1] -- the six gadgets that never read a 1 in [StB] -- all
      survive.  A mutation this local is the sharpest available test
      that the deposit's length really is the walk-back and not a
      fitted constant.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Machines.Counters Require Import Wave4_15.
Import ListNotations.

(** ** Bootstrap anchor *)

(** Distinct anchors are distinguished by [ceqb]. *)
Example w15_anchor_distinct : ceqb (Cf15 2) (Cf15 3) = false.
Proof. reflexivity. Qed.

Example w15_anchor_distinct_7 : ceqb (Cf15 7) (Cf15 8) = false.
Proof. reflexivity. Qed.

(** The boot really reaches [Cf15 2] from the blank tape at 17 steps. *)
Example w15_boot_reaches : match csteps tm_15 17 c0 with
                           | Some c => ceqb c (Cf15 2)
                           | None => false
                           end = true.
Proof. vm_compute. reflexivity. Qed.

(** ...and neither neighbour of 17 does. *)
Example w15_boot_not_16 : match csteps tm_15 16 c0 with
                          | Some c => ceqb c (Cf15 2)
                          | None => false
                          end = false.
Proof. vm_compute. reflexivity. Qed.

Example w15_boot_not_18 : match csteps tm_15 18 c0 with
                          | Some c => ceqb c (Cf15 2)
                          | None => false
                          end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The lap step counts are exact

    [p] even is a single [ruleA] window -- 10 steps, no induction and no
    dependence on the tape's length.  [p] odd pays [entry5 + owcost l +
    6a + deposit + bcost], and those five odd laps are the measured
    ones. *)

Example w15_even_lap_2 : csteps tm_15 10 (Cf15 2) = Some (Cf15 3).
Proof. vm_compute. reflexivity. Qed.

Example w15_even_lap_4 : csteps tm_15 10 (Cf15 4) = Some (Cf15 5).
Proof. vm_compute. reflexivity. Qed.

Example w15_even_lap_16 : csteps tm_15 10 (Cf15 16) = Some (Cf15 17).
Proof. vm_compute. reflexivity. Qed.

Example w15_even_lap_not_9 : csteps tm_15 9 (Cf15 4) <> Some (Cf15 5).
Proof. vm_compute. discriminate. Qed.

Example w15_even_lap_not_11 : csteps tm_15 11 (Cf15 4) <> Some (Cf15 5).
Proof. vm_compute. discriminate. Qed.

Example w15_odd_lap_3 : csteps tm_15 34 (Cf15 3) = Some (Cf15 4).
Proof. vm_compute. reflexivity. Qed.

Example w15_odd_lap_5 : csteps tm_15 38 (Cf15 5) = Some (Cf15 6).
Proof. vm_compute. reflexivity. Qed.

Example w15_odd_lap_7 : csteps tm_15 70 (Cf15 7) = Some (Cf15 8).
Proof. vm_compute. reflexivity. Qed.

Example w15_odd_lap_15 : csteps tm_15 138 (Cf15 15) = Some (Cf15 16).
Proof. vm_compute. reflexivity. Qed.

Example w15_odd_lap_31 : csteps tm_15 270 (Cf15 31) = Some (Cf15 32).
Proof. vm_compute. reflexivity. Qed.

Example w15_odd_lap_3_not_33 : csteps tm_15 33 (Cf15 3) <> Some (Cf15 4).
Proof. vm_compute. discriminate. Qed.

Example w15_odd_lap_5_not_37 : csteps tm_15 37 (Cf15 5) <> Some (Cf15 6).
Proof. vm_compute. discriminate. Qed.

Example w15_odd_lap_7_not_69 : csteps tm_15 69 (Cf15 7) <> Some (Cf15 8).
Proof. vm_compute. discriminate. Qed.

Example w15_odd_lap_15_not_137 : csteps tm_15 137 (Cf15 15) <> Some (Cf15 16).
Proof. vm_compute. discriminate. Qed.

(** The two rules do not share a cost: the even lap's constant 10 is not
    an odd lap, and an odd lap's count is not the even one's. *)
Example w15_rules_do_not_cross_A :
  csteps tm_15 10 (Cf15 3) <> Some (Cf15 4).
Proof. vm_compute. discriminate. Qed.

Example w15_rules_do_not_cross_B :
  csteps tm_15 34 (Cf15 4) <> Some (Cf15 5).
Proof. vm_compute. discriminate. Qed.

(** ** [btail]'s two branches

    The vectors are the measured ones (docs/HOLDOUTS_MXDYS_SN.md 5b), and
    the two ways to misread the deposit are rejected. *)

(** The SPAWN: [3 -> 4] adds ONE to the deposit block and appends a
    length-2 block -- the carry out of the top, i.e. the new leading 1 of
    the positive. *)
Example w15_venc_3 : venc 3 = [3].
Proof. reflexivity. Qed.

Example w15_venc_4 : venc 4 = [4; 2].
Proof. reflexivity. Qed.

(** Reading the spawn as a bare bump (as the interior case does) is the
    trap; there is no [+2] and no missing block. *)
Example w15_spawn_not_bump : venc 4 <> [5].
Proof. discriminate. Qed.

Example w15_spawn_not_plus_two : venc 4 <> [5; 2].
Proof. discriminate. Qed.

(** The INTERIOR deposit: [5 -> 6] adds TWO to the deposit block and ONE
    to the block beyond it.  Both halves are load-bearing. *)
Example w15_venc_5 : venc 5 = [5; 2].
Proof. reflexivity. Qed.

Example w15_venc_6 : venc 6 = [7; 3].
Proof. reflexivity. Qed.

Example w15_interior_moves_next : venc 6 <> [7; 2].
Proof. discriminate. Qed.

Example w15_interior_not_plus_one : venc 6 <> [6; 3].
Proof. discriminate. Qed.

(** The scan stops at the first ODD block, not at the frontier.  At
    [p = 7] the frontier block (8) is EVEN, so the carry rides over it
    and deposits at 3 -- which then spawns.  Depositing at the frontier
    would give [[10; 3]]. *)
Example w15_venc_7 : venc 7 = [8; 3].
Proof. reflexivity. Qed.

Example w15_venc_8 : venc 8 = [8; 4; 2].
Proof. reflexivity. Qed.

Example w15_scan_skips_even : venc 8 <> [10; 3].
Proof. discriminate. Qed.

Example w15_venc_15 : venc 15 = [16; 8; 3].
Proof. reflexivity. Qed.

Example w15_venc_16 : venc 16 = [16; 8; 4; 2].
Proof. reflexivity. Qed.

(** ** The deposit is a SWEEP, not a window

    This is the trap that a 42-context sample and a naive window search
    both miss.  [dep0] (nothing beyond the deposit block) is SIX steps;
    [dep2] (a block beyond) is EIGHT, because [A0 = 1RB] bounces the head
    right into [StB] and [StB] then walks BACK over the 1s just laid.

    The two contexts below are the real ones -- [p = 3]'s deposit and
    [p = 5]'s. *)

(** [dep0], the spawn: six steps, and the head is already home in
    [StC].  The new stripe past the end is fabricated by [chd]/[ctl]. *)
Example w15_dep0_six :
  csteps tm_15 6 (StC, ([S0; S1; S1; S0; S1; S1], S0, [S1; S0]))
  = Some (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S1, [S0])).
Proof. reflexivity. Qed.

Example w15_dep0_not_five :
  csteps tm_15 5 (StC, ([S0; S1; S1; S0; S1; S1], S0, [S1; S0]))
  <> Some (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S1, [S0])).
Proof. vm_compute. discriminate. Qed.

(** [dep2], the interior deposit: EIGHT steps. *)
Example w15_dep2_eight :
  csteps tm_15 8 (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S0,
                        [S1; S0; S1; S1; S0]))
  = Some (StC, ([S1; S1; S1; S1; S1; S0; S1; S1], S1,
                [S0; S1; S1; S1; S0])).
Proof. reflexivity. Qed.

(** And here is the trap, stated: on [dep2]'s context, six steps do NOT
    land where [dep0] says -- they land MID-SWEEP, in [StB], with
    [dep0]'s left list [S0::S1::S1::L] already built.  That is exactly
    the configuration a window search calls a match. *)
Example w15_deposit_is_a_sweep :
  csteps tm_15 6 (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S0,
                        [S1; S0; S1; S1; S0]))
  = Some (StB, ([S0; S1; S1; S1; S1; S1; S1; S0; S1; S1], S1,
                [S1; S1; S0])).
Proof. reflexivity. Qed.

(** ...so [dep0]'s conclusion is false there, at six steps and at seven. *)
Example w15_dep0_wrong_on_dep2 :
  csteps tm_15 6 (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S0,
                        [S1; S0; S1; S1; S0]))
  <> Some (StC, ([S0; S1; S1; S1; S1; S1; S1; S0; S1; S1], S1, [S0; S0])).
Proof. vm_compute. discriminate. Qed.

Example w15_dep2_not_seven :
  csteps tm_15 7 (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S0,
                        [S1; S0; S1; S1; S0]))
  <> Some (StC, ([S1; S1; S1; S1; S1; S0; S1; S1], S1,
                 [S0; S1; S1; S1; S0])).
Proof. vm_compute. discriminate. Qed.

(** ** Unit mutation: break the sweep's walk-back

    [tm_15] with [B1] re-routed to [StC] instead of [StB].  [StB] reading
    a 1 is the deposit's walk-back step and the return sweep's stripe
    crossing, and nothing else in the machine reads a 1 in [StB]. *)
Definition tm_15_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** It kills the interior deposit... *)
Example w15_mut_breaks_dep2 :
  csteps tm_15_mut 8 (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S0,
                            [S1; S0; S1; S1; S0]))
  <> Some (StC, ([S1; S1; S1; S1; S1; S0; S1; S1], S1,
                 [S0; S1; S1; S1; S0])).
Proof. vm_compute. discriminate. Qed.

(** ...the return sweep's stripe crossing... *)
Example w15_mut_breaks_cross7 :
  csteps tm_15_mut 7 (StC, ([S0; S1; S1; S1; S0], S1, [S1; S0]))
  <> Some (StC, ([S1; S0], S1, [S0; S1; S1; S1; S0])).
Proof. vm_compute. discriminate. Qed.

(** ...and the whole no-carry lap, whose sixth step is the same
    walk-back. *)
Example w15_mut_breaks_ruleA :
  csteps tm_15_mut 10 (StC, ([], S0, [S1; S0; S1; S1; S0]))
  <> Some (StC, ([], S0, [S1; S1; S0; S1; S1; S1; S0])).
Proof. vm_compute. discriminate. Qed.

Example w15_mut_breaks_lap :
  csteps tm_15_mut 38 (Cf15 5) <> Some (Cf15 6).
Proof. vm_compute. discriminate. Qed.

(** The genuine machine does hold on all four windows... *)
Example w15_genuine_cross7 :
  csteps tm_15 7 (StC, ([S0; S1; S1; S1; S0], S1, [S1; S0]))
  = Some (StC, ([S1; S0], S1, [S0; S1; S1; S1; S0])).
Proof. reflexivity. Qed.

Example w15_genuine_ruleA :
  csteps tm_15 10 (StC, ([], S0, [S1; S0; S1; S1; S0]))
  = Some (StC, ([], S0, [S1; S1; S0; S1; S1; S1; S0])).
Proof. reflexivity. Qed.

(** ...and the mutation is local enough that the six gadgets which never
    read a 1 in [StB] survive it unchanged.  So the failures above are
    the SWEEP's, not a blanket break: the outward phase is untouched and
    only the walk-back dies. *)

Example w15_mut_keeps_out6 :
  csteps tm_15_mut 6 (StC, ([S0; S1; S0], S0, [S1; S1; S1; S0; S1]))
  = Some (StC, ([S0; S1; S1; S1; S0], S0, [S1; S0; S1])).
Proof. vm_compute. reflexivity. Qed.

Example w15_mut_keeps_entry5 :
  csteps tm_15_mut 5 (StC, ([], S0, [S1; S1; S0; S1; S1; S0]))
  = Some (StC, ([S0; S0; S1; S1], S0, [S1; S1; S0])).
Proof. vm_compute. reflexivity. Qed.

Example w15_mut_keeps_carry5 :
  csteps tm_15_mut 5 (StC, ([S0; S1; S0], S0, [S1; S1; S0; S1; S0]))
  = Some (StC, ([S0; S0; S1; S1; S1; S0], S0, [S1; S0])).
Proof. vm_compute. reflexivity. Qed.

Example w15_mut_keeps_dep0 :
  csteps tm_15_mut 6 (StC, ([S0; S1; S1; S0; S1; S1], S0, [S1; S0]))
  = Some (StC, ([S0; S1; S1; S1; S1; S0; S1; S1], S1, [S0])).
Proof. vm_compute. reflexivity. Qed.

Example w15_mut_keeps_ret1 :
  csteps tm_15_mut 1 (StC, ([S1; S0], S1, [S1; S0]))
  = Some (StC, ([S0], S1, [S1; S1; S0])).
Proof. vm_compute. reflexivity. Qed.

Example w15_mut_keeps_exit1 :
  csteps tm_15_mut 1 (StC, ([], S1, [S1; S0]))
  = Some (StC, ([], S0, [S1; S1; S0])).
Proof. vm_compute. reflexivity. Qed.
