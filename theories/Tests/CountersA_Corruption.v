(** * CountersA_Corruption: negative controls, counters session A.

    Corruption tests for the machines boarded by the second counters
    session (gray / mono2 / double / blockdbl families), in the BBB
    tradition: every computable ingredient must REJECT mutated
    inputs -- walls that are too small, wrong periods, wrong claimed
    exits, one-transition mutant machines, wrong bootstrap anchors.
    Everything is decided by [vm_compute]/[discriminate]. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** ** gray_counter #19 (Gray_19) *)

From BBB4.Machines.Counters Require Import Gray_19.

(** Wall discipline: the left-edge turnaround needs the tape edge --
    with the left wall ON it must die, not fabricate blanks. *)
Example wall_U6e_19 : wsteps true true tm_19 3 (StB, ([S1], S0, []))
                      = None.
Proof. reflexivity. Qed.

(** The overflow gap push runs into blank territory: walled right it
    dies. *)
Example wall_U8e_19 : wsteps true true tm_19 2 (StC, ([], S0, []))
                      = None.
Proof. reflexivity. Qed.

(** The overflow marker clear steps past the last set cell. *)
Example wall_U7e_19 : wsteps true true tm_19 2 (StD, ([], S0, [S1]))
                      = None.
Proof. reflexivity. Qed.

(** The comb crossing takes exactly 4 steps: at 3 the head is
    mid-unit. *)
Example U2_wrong_period_19 :
  wsteps true true tm_19 3 (StC, ([], S0, [S1; S0; S1; S0]))
  <> Some (StC, ([S0; S1; S0; S1], S0, [])).
Proof. discriminate. Qed.

(** The crossing deposits the SHIFTED comb (0101 nearest-first),
    not the original phase. *)
Example U2_wrong_exit_19 :
  wsteps true true tm_19 4 (StC, ([], S0, [S1; S0; S1; S0]))
  <> Some (StC, ([S1; S0; S1; S0], S0, [])).
Proof. discriminate. Qed.

(** #19 with D0 -> 1RC instead of 1RD: the crossing fires D0. *)
Definition tm_19_mutD0 : TM := fun q s =>
  match q, s with
  | StD, S0 => mk S1 DR StC
  | _, _ => tm_19 q s
  end.

Example mutD0_breaks_U2_19 :
  wsteps true true tm_19_mutD0 4 (StC, ([], S0, [S1; S0; S1; S0]))
  <> Some (StC, ([S0; S1; S0; S1], S0, [])).
Proof. discriminate. Qed.

(** #19 with B1 -> 0LC instead of 0LB: the return sweep's clearing
    run fires B1 every step. *)
Definition tm_19_mutB1 : TM := fun q s =>
  match q, s with
  | StB, S1 => mk S0 DL StC
  | _, _ => tm_19 q s
  end.

Example mutB1_breaks_UB1_19 :
  wsteps true true tm_19_mutB1 1 (StB, ([S1], S1, []))
  <> Some (StB, ([], S1, [S0])).
Proof. discriminate. Qed.

Example mutD0_breaks_boot_19 :
  match csteps tm_19_mutD0 64 c0 with
  | Some c => ceqb c (Gray_19.Cc 3)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** The 64-step bootstrap lands on S(3), not S(4). *)
Example boot_wrong_anchor_19 :
  match csteps tm_19 64 c0 with
  | Some c => ceqb c (Gray_19.Cc 4)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** Gray-encoding sanity: the flip slot follows the carry view.
    G(4) = 6 (slots 1,2), G(5) = 7 (slots 0,1,2), G(7) = 4. *)
Example Wg_4 : Wg 4 = [S0; S0; S0; S1; S0; S0; S1].
Proof. reflexivity. Qed.

Example Wg_5 : Wg 5 = [S1; S0; S0; S1; S0; S0; S1].
Proof. reflexivity. Qed.

Example Wg_7_overflow : Wg 7 = [S0; S0; S0; S0; S0; S0; S1].
Proof. reflexivity. Qed.

(** The decomposition is rigid: W(4)'s head slot is clear, so a
    claimed set head slot is rejected. *)
Example Wg4_not_set : forall w, Wg 4 <> S1 :: w.
Proof. intros w H. discriminate H. Qed.
