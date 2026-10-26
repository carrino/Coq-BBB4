From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Spec Witness Mirror.
From SmallBB.Checkers Require Import TCycler.
Import ListNotations.

(** 0LB---_1RA1LB *)
Definition champion22_state : TM := machine_of_codes 2 2 [1 ; 12 ; 6 ; 5].
Lemma champion22_state_admissible : Admissible 2 2 champion22_state.
Proof.
  split.
  - intros [] [] tr H; cbv [champion22_state machine_of_codes nat_trans st_index sym_index nth] in H;
      try discriminate; injection H as <-; unfold output_ok; simpl; lia.
  - intros [] [] H; simpl in H; try (exfalso; lia); reflexivity.
Qed.

(** 0LB1RB_1RA1LB *)
Definition champion22_instr : TM := machine_of_codes 2 2 [1 ; 7 ; 6 ; 5].
Lemma champion22_instr_admissible : Admissible 2 2 champion22_instr.
Proof.
  split.
  - intros [] [] tr H; cbv [champion22_instr machine_of_codes nat_trans st_index sym_index nth] in H;
      try discriminate; injection H as <-; unfold output_ok; simpl; lia.
  - intros [] [] H; simpl in H; try (exfalso; lia); reflexivity.
Qed.

(** 1LB0RB_1RA0LC_1RC1RA *)
Definition champion32 : TM := machine_of_codes 3 2 [7 ; 4 ; 9 ; 2 ; 11 ; 9].
Lemma champion32_admissible : Admissible 3 2 champion32.
Proof.
  split.
  - intros [] [] tr H; cbv [champion32 machine_of_codes nat_trans st_index sym_index nth] in H;
      try discriminate; injection H as <-; unfold output_ok; simpl; lia.
  - intros [] [] H; simpl in H; try (exfalso; lia); reflexivity.
Qed.

(** 1LB2RB1RA_2RB2LA0LA *)
Definition champion23_state : TM := machine_of_codes 2 3 [5 ; 11 ; 6 ; 11 ; 8 ; 0].
Lemma champion23_state_admissible : Admissible 2 3 champion23_state.
Proof.
  split.
  - intros [] [] tr H; cbv [champion23_state machine_of_codes nat_trans st_index sym_index nth] in H;
      try discriminate; injection H as <-; unfold output_ok; simpl; lia.
  - intros [] [] H; simpl in H; try (exfalso; lia); reflexivity.
Qed.

(** 1LB2RA0LB_1RA0RB1LA *)
Definition champion23_instr : TM := machine_of_codes 2 3 [5 ; 10 ; 1 ; 6 ; 3 ; 4].
Lemma champion23_instr_admissible : Admissible 2 3 champion23_instr.
Proof.
  split.
  - intros [] [] tr H; cbv [champion23_instr machine_of_codes nat_trans st_index sym_index nth] in H;
      try discriminate; injection H as <-; unfold output_ok; simpl; lia.
  - intros [] [] H; simpl in H; try (exfalso; lia); reflexivity.
Qed.

Lemma champion22_state_quiet : QuietAfter champion22_state StA 5.
Proof.
  let c := eval vm_compute in (csteps champion22_state 5 c0) in
  lazymatch c with Some ?cc => apply (halt_quiet_state champion22_state 5 cc) end;
  vm_compute; reflexivity.
Qed.
Lemma champion22_instr_quiet : QuietAfterTr champion22_instr (StA,S0) 7.
Proof.
  apply mirror_quiet_tr. apply (tr_witness_sound (mirror_tm champion22_instr) 8 5 0 (StA,S0) 7).
  vm_compute; reflexivity.
Qed.
Lemma champion32_state_quiet : QuietAfter champion32 StB 54.
Proof.
  exact (proj1 (proj2 (tcycler_check_qh_sound champion32 55 1 0 StB 54 ltac:(vm_compute; reflexivity)))).
Qed.
Lemma champion32_instr_quiet : QuietAfterTr champion32 (StB,S1) 54.
Proof. apply (tr_witness_sound champion32 55 1 0 (StB,S1) 54). vm_compute; reflexivity. Qed.
Lemma champion23_state_quiet : QuietAfter champion23_state StA 58.
Proof.
  exact (proj1 (proj2 (tcycler_check_qh_sound champion23_state 59 1 0 StA 58 ltac:(vm_compute; reflexivity)))).
Qed.
Lemma champion23_instr_quiet : QuietAfterTr champion23_instr (StA,S2) 66.
Proof. apply (tr_witness_sound champion23_instr 75 4 0 (StA,S2) 66). vm_compute; reflexivity. Qed.
