From Coq Require Import List Arith Bool NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn19FiniteCounter Require Import FiniteCounter Trace.
Import ListNotations.

Example actual_entry : csteps fc_tm 45 c0=Some(fc_X 6 0).
Proof. reflexivity. Qed.
Example three_context :
 csteps fc_tm 7(fc_back StA[S2;S3;S0][S2;S2;S3;S1;S2])=
 Some(fc_back StA[S3;S0][S2;S2;S2;S2;S1;S2]).
Proof. reflexivity. Qed.
Example one_context :
 csteps fc_tm 7(fc_back StA[S2;S3;S0][S2;S2;S1;S1;S2])=
 Some(fc_back StA[S3;S0][S2;S2;S3;S2;S1;S2]).
Proof. reflexivity. Qed.
Example quadratic_B_flatten :
 csteps fc_tm 14(fc_phase 1[S2;S2;S3;S1])=Some(fc_phase 5[S3;S1]).
Proof. reflexivity. Qed.
Example remainder_zero : csteps fc_tm 47(fc_X 2 0)=Some(fc_L 8).
Proof. reflexivity. Qed.
Example remainder_one : csteps fc_tm 63(fc_X 2 1)=Some(fc_X 4 6).
Proof. reflexivity. Qed.
Example remainder_two_drift : csteps fc_tm 119(fc_X 2 2)=Some(fc_phase 13[]).
Proof. reflexivity. Qed.
Example remainder_three : csteps fc_tm 35(fc_X 2 3)=Some(fc_M 6 1).
Proof. reflexivity. Qed.
Example decrement_four : csteps fc_tm 33(fc_X 2 5)=Some(fc_X 7 1).
Proof. reflexivity. Qed.
Example singleton_prefix : csteps fc_tm 5(fc_L 3)=Some(fc_M 1 3).
Proof. reflexivity. Qed.
Example mixed_one : csteps fc_tm 45(fc_M 1 3)=Some(fc_X 6 2).
Proof. reflexivity. Qed.
Example mixed_tail : csteps fc_tm 49(fc_M 2 1)=Some(fc_X 6 2).
Proof. reflexivity. Qed.
Example drift_state_stays_B : forall t,
 exists l n,csteps fc_tm t(fc_phase 13[])=Some(StB,(l,S0,repeat S0 n)).
Proof. intro t;unfold fc_phase;rewrite app_nil_r;apply fc_B_drift. Qed.
Example exact_long_prefix :
 csteps fc_tm(fc_count 1012664081%N)c0=Some(fc_phase(fc_count 34861%N)[]).
Proof. exact fc_native_prefix. Qed.
