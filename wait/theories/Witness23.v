(** Lower-bound witnesses for two-state ternary waiting times. *)
From Coq Require Import List Arith Lia.
From SmallBB Require Import Statement StatementTr Size.
From BBBWait Require Import Spec SpecTr Witness32.
Import ListNotations.

(** Right-hand form 1RB2LA1RA_1LB1LA2RB, targeting state B. *)
Definition wait23_champion_state := machine_of_codes 2 3 [7;8;6;5;4;11].
Lemma wait23_champion_state_admissible : Admissible 2 3 wait23_champion_state.
Proof.
  split.
  - intros q s tr E; destruct q,s; cbn in E; try discriminate;
      injection E as <-; unfold output_ok; cbn; lia.
  - intros q s H; destruct q,s; cbn in H; try lia; reflexivity.
Qed.
Lemma wait23_state_checked : state_delay_check wait23_champion_state 59 32 StB = true.
Proof. vm_compute; reflexivity. Qed.
Theorem wait23_state_minimal : forall w, WaitBound 2 3 59 w -> 32 <= w.
Proof.
  eapply state_delay_minimal; [exact wait23_champion_state_admissible|exact wait23_state_checked].
Qed.

(** Right-hand form 1RB2LA1RA_1LA2RA2RB, targeting instruction B1. *)
Definition wait23_champion_instr := machine_of_codes 2 3 [7;8;6;4;10;11].
Lemma wait23_champion_instr_admissible : Admissible 2 3 wait23_champion_instr.
Proof.
  split.
  - intros q s tr E; destruct q,s; cbn in E; try discriminate;
      injection E as <-; unfold output_ok; cbn; lia.
  - intros q s H; destruct q,s; cbn in H; try lia; reflexivity.
Qed.
Lemma wait23_instr_checked : instr_delay_check wait23_champion_instr 67 693 (StB,S1) = true.
Proof. vm_compute; reflexivity. Qed.
Theorem wait23_instr_minimal : forall w, WaitBoundTr 2 3 67 w -> 693 <= w.
Proof.
  eapply instr_delay_minimal; [exact wait23_champion_instr_admissible|exact wait23_instr_checked].
Qed.
