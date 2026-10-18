(** Sliding-window seeding is equal to the original indexed enumeration
    for every input (ng_seed_side_spec and seed_ok_side_spec). These tests
    pin the padding boundaries and exercise both evaluators and the checker. *)
From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram NGramTr.
Import ListNotations.

Example empty_tape : ng_seed_side 2 [] = [[S0; S0]].
Proof. vm_compute. reflexivity. Qed.

Example one_cell : ng_seed_side 2 [S1] = [[S0; S0]; [S0; S0]].
Proof. native_compute. reflexivity. Qed.

Example padding_and_final_offset :
  ng_seed_side 3 [S1; S1; S1] =
  [[S1; S1; S0]; [S1; S0; S0]; [S0; S0; S0]; [S0; S0; S0]].
Proof. native_compute. reflexivity. Qed.

Example zero_width : ng_seed_side 0 [S1; S0] = [[]; []; []].
Proof. vm_compute. reflexivity. Qed.

Definition drift : TM := fun _ _ => Some (mkTrans S1 DR StA).
Example accept_drifter : ngram_check_neverqh drift 2 4 256 32 = true.
Proof. native_compute. reflexivity. Qed.

Example reject_exhausted_checker : ngram_check_neverqh drift 2 0 0 8 = false.
Proof. vm_compute. reflexivity. Qed.
Example reject_empty_grams : ng_seed_ok 2 gempty gempty c0 = false.
Proof. native_compute. reflexivity. Qed.

Print Assumptions ng_seed_side_spec.
Print Assumptions seed_ok_side_spec.
Print Assumptions ngram_check_neverqh_sound.
Print Assumptions ngram_check_neverqhtr_sound.
