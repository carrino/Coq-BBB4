From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20FibonacciCounter Require Import FibonacciCounter.
Import ListNotations.
Example actual_blank_entry : csteps fc_tm 24 c0=Some(fc_main 1 0).
Proof. reflexivity. Qed.
Example zero_left_block_is_admissible : csteps fc_tm 37(fc_main 0 0)=Some(fc_main 2 0).
Proof. reflexivity. Qed.
Example first_actual_growth : csteps fc_tm 57(fc_main 1 0)=Some(fc_main 2 1).
Proof. reflexivity. Qed.
Example pair_scan_context : csteps fc_tm 4(fc_front StA[S0;S1][S3;S3;S3;S3;S2;S3])=
 Some(fc_front StA[S2;S2;S2;S2;S0;S1][S2;S3]).
Proof. reflexivity. Qed.
Example wall_even_boundary : csteps fc_tm 6(fc_front StA[S2;S2;S3;S0][S2;S3])=
 Some(fc_front StA[S2;S2;S2;S0][S1;S3]).
Proof. reflexivity. Qed.
Example open_even_boundary : csteps fc_tm 16(fc_front StA[S2;S2][S2;S1;S2])=
 Some(fc_front StA[S2;S3][S1;S3;S3;S1;S2]).
Proof. reflexivity. Qed.
Example open_zero_boundary : csteps fc_tm 3(fc_front StA[][S2;S1;S0])=
 Some(fc_front StA[][S3;S3;S1;S0]).
Proof. reflexivity. Qed.
Example one_pair_drain : csteps fc_tm 34(fc_Q 0 1 0)=Some(fc_Q 1 0 1).
Proof. reflexivity. Qed.
Example zero_drain : csteps fc_tm(fc_drain_cost 3 0)(fc_Q 3 0 4)=Some(fc_Q 3 0 4).
Proof. reflexivity. Qed.
Example finish_boundary : csteps fc_tm 32(fc_Q 0 0 1)=Some(fc_main 3 0).
Proof. reflexivity. Qed.
Example bad_block_parity_exposes_blank_B : csteps fc_tm 27(StA,([S2;S1;S3],S0,[]))=
 Some(StB,([S2;S2;S2;S1;S2;S3],S0,[])).
Proof. reflexivity. Qed.
Example altered_wall_invalidates_even_macro : csteps fc_tm 2(fc_front StA[S0][S2;S3])<>
 Some(fc_front StA[S2][S1;S3]).
Proof. discriminate. Qed.
Example frozen_A3_enters_B : fc_tm StA S3=Some(mkTrans S2 DR StB).
Proof. reflexivity. Qed.
Example altered_A3_is_distinct : fc_tm StA S3<>Some(mkTrans S2 DR StA).
Proof. discriminate. Qed.
