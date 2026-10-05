(** * ChampionTr_Corruption: negative controls for the instruction-level witness.

    [champion_quiet_after_D0] (BBBT4_Champion.v) rests on one binary-fuel
    [vm_compute]: at configuration index 32,779,477 the champion is in
    [StD] reading [S0], so instruction (D, 0) fires there.  The pairing
    of index, state and symbol must be RIGID; each check below is the
    same computation with one of the three moved, and must fail:

    - the other instruction of [StD], (D, 1), does not fire at
      32,779,477 -- the witness cannot be relabelled;
    - (D, 0) does not fire at the landing, 32,779,478 -- the score
      cannot be inflated by one;
    - the instruction fired at the landing is (C, 0), the start of the
      terminal C-loop -- positive control that the run reads the
      landing the state proof expects.

    Each is one ~10 s [vm_compute]; a regression that made either
    negative check pass would be a soundness alarm. *)

From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.
Import ListNotations.

Definition fires_instr (q : St) (a : Sym) (oc : option cconf) : bool :=
  match oc with
  | Some (q', (_, h, _)) => st_eqb q' q && sym_eqb h a
  | None => false
  end.

(** (D, 1) does not fire at 32,779,477. *)
Example champion_D1_not_at_prev :
  fires_instr StD S1 (cstepsN tm_champion champ_prevN c0) = false.
Proof. vm_compute. reflexivity. Qed.

(** (D, 0) does not fire at the landing, 32,779,478. *)
Example champion_D0_not_at_landing :
  fires_instr StD S0 (cstepsN tm_champion champ_scoreN c0) = false.
Proof. vm_compute. reflexivity. Qed.

(** Positive control: (C, 0) fires at the landing. *)
Example champion_C0_at_landing :
  fires_instr StC S0 (cstepsN tm_champion champ_scoreN c0) = true.
Proof. vm_compute. reflexivity. Qed.
