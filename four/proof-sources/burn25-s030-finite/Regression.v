From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge Trace Final.
Import ListNotations.
Example sf_reg_entry : csteps s30_tm 3 c0=Some(s30_Q 1[]).
Proof. exact s30_entry. Qed.
Example sf_reg_sentinel_context : csteps s30_tm 8(s30_Q 3[S0;S3;S2;S1])=
 Some(s30_Q 1[S1;S1;S1;S0;S1;S3;S2;S1]).
Proof. exact(s30_zero 3[S3;S2;S1]). Qed.
Example sf_reg_pair_context : csteps s30_tm 30(s30_Q 2[S1;S1;S3;S0;S2])=
 Some(s30_Q 7[S3;S0;S2]).
Proof. exact(s30_pair 2[S3;S0;S2]). Qed.
Example sf_reg_101_context : csteps s30_tm 31(s30_Q 2[S1;S0;S1;S2;S3])=
 Some(s30_Q 8[S2;S3]).
Proof. exact(s30_onezeroone 2[S2;S3]). Qed.
Example sf_reg_plain_phase : csteps s30_tm(sf_count 92898%N)c0=
 Some(s30_Q(sf_count 362%N)(sf_word 0%N false 0%N)).
Proof. exact sf_prefix_13. Qed.
Example sf_reg_missing_sentinel : csteps s30_tm 24(s30_Q 1[S1])<>Some(s30_Q 6[]).
Proof. vm_compute;discriminate. Qed.
Example sf_reg_binary_suffix : forall n,exists l h r,csteps s30_tm n(StB,([],S2,[S0;S2]))=
 Some(StB,(l,h,r))/\s30_binary l h r.
Proof. intro n;apply s30_B_binary;unfold s30_binary;repeat split;repeat constructor;auto;right;reflexivity. Qed.
Example sf_reg_exact_last_A : QuietAfter s30_tm StA(sf_count 1367354345128%N).
Proof. exact sf_last_A. Qed.
