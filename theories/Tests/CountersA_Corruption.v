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

(** ** mono2_counter #38/#39 (Mono2_38, Mono2_39) *)

From BBB4.Machines.Counters Require Import Mono2_38 Mono2_39.

(** The twins share A/B/D and differ only in C0: each machine's
    prologue fails on the other's exit. *)
Example twins_differ_U1 :
  wsteps false true tm_38 7 (StC, ([], S1, [S1]))
  <> Some (StD, ([S1; S1; S0; S1], S1, [])).
Proof. discriminate. Qed.

Example twins_differ_UP1 :
  wsteps false true tm_39 7 (StB, ([], S1, [S0]))
  <> Some (StD, ([S1; S0; S1; S1], S0, [])).
Proof. discriminate. Qed.

(** Wall discipline: the overflow increment needs the right edge. *)
Example wall_U4e_39 : wsteps true true tm_39 2 (StD, ([], S1, []))
                      = None.
Proof. reflexivity. Qed.

Example wall_U4e_38 : wsteps true true tm_38 2 (StD, ([], S1, []))
                      = None.
Proof. reflexivity. Qed.

(** The prologue materializes cells at the left edge: walled it
    dies. *)
Example wall_U1_39 : wsteps true true tm_39 7 (StC, ([], S1, [S1]))
                     = None.
Proof. reflexivity. Qed.

Example wall_UP2_38 : wsteps true true tm_38 4 (StB, ([], S1, []))
                      = None.
Proof. reflexivity. Qed.

(** Wrong period: the comb crossing takes 3 steps, not 2. *)
Example U2_wrong_period_39 :
  wsteps true true tm_39 2 (StD, ([], S1, [S1; S0; S1]))
  <> Some (StD, ([S1; S1; S0], S1, [])).
Proof. discriminate. Qed.

(** Wrong exit: the climb clears the marker and keeps the bit, not
    the other way around. *)
Example U3_wrong_exit_39 :
  wsteps true true tm_39 2 (StD, ([], S1, [S1; S1]))
  <> Some (StD, ([S0; S1], S1, [])).
Proof. discriminate. Qed.

(** #39 with D1 -> 0RB instead of 0RA breaks the crossing. *)
Definition tm_39_mutD1 : TM := fun q s =>
  match q, s with
  | StD, S1 => mk S0 DR StB
  | _, _ => tm_39 q s
  end.

Example mutD1_breaks_U2_39 :
  wsteps true true tm_39_mutD1 3 (StD, ([], S1, [S1; S0; S1]))
  <> Some (StD, ([S1; S1; S0], S1, [])).
Proof. discriminate. Qed.

Example mutD1_breaks_boot_39 :
  match csteps tm_39_mutD1 38 c0 with
  | Some c => ceqb c (Mono2_39.Cc 3)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** Wrong bootstrap anchors are rejected. *)
Example boot_wrong_anchor_39 :
  match csteps tm_39 38 c0 with
  | Some c => ceqb c (Mono2_39.Cc 4)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example boot_wrong_anchor_38 :
  match csteps tm_38 125 c0 with
  | Some c => ceqb c (Mono2_38.Cc 4)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** Interleaved-marker encoding sanity: Wm2(6) = markers with the
    bits of v = 2 (k = 2), and the overflow shape at 2^k - 1. *)
Example Wm2_6 : Wm2 6 = [S1; S0; S1; S1; S1].
Proof. reflexivity. Qed.

Example Wm2_7_overflow : Wm2 7 = [S1; S1; S1; S1; S1].
Proof. reflexivity. Qed.

Example Wm2_8 : Wm2 8 = [S1; S0; S1; S0; S1; S0; S1].
Proof. reflexivity. Qed.

(** The marker discipline is rigid: a working area starting with a
    clear cell is not a codeword tail. *)
Example Wm2_head_marker : forall p w, Wm2 p <> S0 :: w.
Proof.
  intros p w H.
  destruct (Wm2_head p) as (w' & Hw').
  rewrite Hw' in H. discriminate H.
Qed.
