From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17DoubleZeroRank Require Import DoubleZeroRank.
Import ListNotations.

Example actual_entry : csteps dr_tm 9 c0=Some(dr_main 0).
Proof. reflexivity. Qed.
Example direct_decrement :
 csteps dr_tm 8(dr_config[S3][S2;S1])=Some(dr_config[S3][S0;S1]).
Proof. reflexivity. Qed.
Example carry_decrement :
 csteps dr_tm 16(dr_config[S2][S0;S0;S2;S3])=Some(dr_config[S2][S2;S2;S0;S3]).
Proof. reflexivity. Qed.
Example empty_bit_word_is_safe :
 csteps dr_tm 7(dr_config[][S1])=Some(dr_front StA[S0;S0][S3]).
Proof. reflexivity. Qed.
Example zero_finish_context :
 csteps dr_tm 13(dr_config[S3][S0;S0;S1;S2])=
 Some(dr_front StA[S2;S2;S0;S0;S3][S3;S2]).
Proof. reflexivity. Qed.
Example first_growth : csteps dr_tm 21(dr_main 0)=Some(dr_main 1).
Proof. reflexivity. Qed.
Example changed_outer_zero_invalid_finish :
 csteps dr_tm 7(dr_back StB[S0;S3][S1])<>Some(dr_front StA[S0;S3][S3]).
Proof. discriminate. Qed.
Example absent_terminal_invalid_finish :
 csteps dr_tm 7(dr_config[][])<>Some(dr_front StA[S0;S0][S3]).
Proof. discriminate. Qed.
