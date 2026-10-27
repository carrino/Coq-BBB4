(** Four-symbol acceptance and rejection checks for the n-gram tier. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement CTape Bounds PosEnc NGramCensus.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

(** The startup writes two S3 cells; the recurrent suffix reads S3 in both
    states. A missing S3 branch cannot be hidden by a blank-only example. *)
Definition s3_oscillator : TM := fun q s =>
  match q, s with
  | StA, S0 | StA, S3 => Some (mkTrans S3 DR StB)
  | StB, S0 | StB, S3 => Some (mkTrans S3 DL StA)
  | _, _ => None
  end.

Example accepts_s3_suffix :
  ng_check 2%N 2%N s3_oscillator 1 2 32 4 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem s3_suffix_bounds :
  NonHalt s3_oscillator /\ Bounds 2%N 2%N s3_oscillator.
Proof. eapply ng_check_sound; exact accepts_s3_suffix. Qed.

Definition s3_halts : TM := fun q s =>
  match q, s with
  | StA, S3 => None
  | _, _ => s3_oscillator q s
  end.

Example rejects_s3_halt :
  ng_check 2%N 2%N s3_halts 1 2 32 4 = false.
Proof. vm_compute. reflexivity. Qed.

Example rejects_late_prefix :
  ng_check 1%N 1%N s3_oscillator 1 2 32 4 = false.
Proof. vm_compute. reflexivity. Qed.

Example rejects_zero_width :
  ng_check 2%N 2%N s3_oscillator 0 2 32 4 = false.
Proof. vm_compute. reflexivity. Qed.

(** Every possible unknown boundary symbol has a successor, including S3. *)
Definition all_single_grams := gadds [[S0];[S1];[S2];[S3]] gempty.
Example four_boundary_successors :
  option_map (@length cconf)
    (ng_succs s3_oscillator all_single_grams all_single_grams
      (StA, ([S0], S0, [S0]))) = Some 4.
Proof. vm_compute. reflexivity. Qed.

Example count_s3_and_nonblank : nc1 C3 S3 = 1 /\ nc1 CN S3 = 1.
Proof. split; reflexivity. Qed.
