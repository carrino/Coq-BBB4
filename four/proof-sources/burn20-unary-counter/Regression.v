From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20UnaryCounter Require Import UnaryCounter.
Import ListNotations.
Example actual_blank_entry : csteps uc_tm 3 c0=Some(uc_main 0).
Proof. reflexivity. Qed.
Example empty_unary_growth : csteps uc_tm 7(uc_main 0)=Some(uc_main 1).
Proof. reflexivity. Qed.
Example first_nonempty_growth : csteps uc_tm 27(uc_main 1)=Some(uc_main 2).
Proof. reflexivity. Qed.
Example iteration_context : csteps uc_tm 15
 (uc_front StA[S2;S1;S1;S3][S3;S3;S3;S1;S2])=
 Some(uc_front StA[S2;S1;S3][S3;S3;S3;S3;S0;S2]).
Proof. reflexivity. Qed.
Example odd_drain_toggles_terminal : csteps uc_tm(uc_drain_cost 3 1)
 (uc_front StA[S2;S1;S1;S1;S3][S3;S3;S1;S2])=
 Some(uc_front StA[S2;S3][S3;S3;S3;S3;S3;S0;S2]).
Proof. reflexivity. Qed.
Example zero_drain_preserves_context : csteps uc_tm(uc_drain_cost 0 2)
 (uc_front StA[S2;S0][S3;S3;S3;S0;S1])=
 Some(uc_front StA[S2;S0][S3;S3;S3;S0;S1]).
Proof. reflexivity. Qed.
Example finish_with_nonblank_context : csteps uc_tm 17
 (uc_front StA[S2;S2][S3;S3;S0;S2;S1])=
 Some(uc_front StA[S2;S1;S1;S1;S1;S2][S2;S1]).
Proof. reflexivity. Qed.
Example wrong_finish_bit_is_unsafe : csteps uc_tm 17
 (uc_front StA[S2;S2][S3;S3;S1])<>
 Some(uc_front StA[S2;S1;S1;S1;S1;S2][]).
Proof. discriminate. Qed.
Example missing_two_support_breaks_scan : csteps uc_tm 3
 (uc_front StA[S1][S3;S0])<>Some(uc_front StA[S2;S2][S0]).
Proof. discriminate. Qed.
Example frozen_A2_is_2RA : uc_tm StA S2=Some(mkTrans S2 DR StA).
Proof. reflexivity. Qed.
Example altered_A2_write_is_distinct : uc_tm StA S2<>Some(mkTrans S0 DR StA).
Proof. discriminate. Qed.
