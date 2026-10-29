(** Finite ends and history cells retain all four symbols. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds NGramRegression FiniteCensus HistCensus.
From BBB24.Checkers Require Import NGram FiniteNGram NGramHist.
Import ListNotations.

Example finite_s3_acceptance :
  fn_check_mode false 2%N 2%N s3_oscillator 1 2 32 4 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem finite_s3_bounds :
  NonHalt s3_oscillator /\ Bounds 2%N 2%N s3_oscillator.
Proof. exact (fn_check_mode_sound false 2%N 2%N s3_oscillator 1 2 32 4 finite_s3_acceptance). Qed.

Example history_s3_acceptance :
  hn_check_mode false 4%N 4%N s3_oscillator 1 1 4 32 4 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem history_s3_bounds :
  NonHalt s3_oscillator /\ Bounds 4%N 4%N s3_oscillator.
Proof. exact (hn_check_mode_sound false 4%N 4%N s3_oscillator 1 1 4 32 4 history_s3_acceptance). Qed.

Example finite_state_acceptance :
  fn_check_mode true 2%N 2%N s3_oscillator 1 2 32 4 = true.
Proof. vm_compute. reflexivity. Qed.
Example history_state_acceptance :
  hn_check_mode true 4%N 4%N s3_oscillator 1 1 4 32 4 = true.
Proof. vm_compute. reflexivity. Qed.

Example reject_s3_halt :
  fn_check_mode false 2%N 2%N s3_halts 1 2 32 4 = false /\
  hn_check_mode false 2%N 2%N s3_halts 1 1 2 32 4 = false.
Proof. vm_compute. split; reflexivity. Qed.
Example reject_late_state_prefix :
  fn_check_mode true 1%N 1%N s3_oscillator 1 2 32 4 = false /\
  hn_check_mode true 1%N 1%N s3_oscillator 1 1 4 32 4 = false.
Proof. vm_compute. split; reflexivity. Qed.

(** The finite-window pop includes both the exact end and all four symbols. *)
Example finite_pop_s3 :
  fn_pops 1 (gadds [[];[S0];[S1];[S2];[S3]] gempty) [S0] =
    [[];[S0];[S1];[S2];[S3]].
Proof. vm_compute. reflexivity. Qed.
