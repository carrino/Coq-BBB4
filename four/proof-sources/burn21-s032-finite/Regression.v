(** Imported boundary and composition regressions. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn21S032Finite Require Import CutMacros BinaryBridge Trace Final.
Import ListNotations.
Example sf_reg_actual_entry : csteps sc_tm 122 c0=Some(sc_cut 2(repeat S3 13++[S1])).
Proof. exact sc_prefix122. Qed.
Example sf_reg_bulk_context : csteps sc_tm(sf_count 25%N)
 (sc_cut(sf_count 2%N)[S3;S3;S0;S1;S3])=Some(sc_cut(sf_count 7%N)[S0;S1;S3]).
Proof. pose proof(sf_N_bulk 1%N 2%N [S0;S1;S3])as H;change(csteps sc_tm(sf_count 25%N)(sc_cut(sf_count 2%N)(repeat S3(sf_count 2%N)++[S0;S1;S3]))=Some(sc_cut(sf_count 7%N)[S0;S1;S3]))in H;rewrite sf_r2 in H;exact H. Qed.
Example sf_reg_left_guard : csteps sc_tm 25(StA,([S1],S0,[S2;S2;S3;S3]))<>Some(sc_cut 7[]).
Proof. vm_compute;discriminate. Qed.
Example sf_reg_bridge : csteps sc_tm 24(sc_cut 2[S3;S0;S3;S1])=Some(sc_Q 8[S1]).
Proof. exact(sc_cut_three_zero_three 2[S1]). Qed.
Example sf_reg_synthetic_exposure : forall a,csteps sc_tm(a+14)(sc_cut a[S3])=
 Some(StB,(S2::repeat S1(a+3),S0,[])).
Proof. exact sc_unprotected_three. Qed.
Example sf_reg_original_exposure : csteps sc_tm(sf_count 67093892229058240%N)c0=
 Some(sc_cut(sf_count 530843041%N)[S3]).
Proof. exact sf_final_cut. Qed.
Example sf_reg_exact_last_A : QuietAfter sc_tm StA(sf_count 67093892759901294%N).
Proof. exact sf_last_A. Qed.
Example sf_reg_uniform_bound : NonHalt sc_tm /\QHBound(N.to_nat 72057594037927936%N)sc_tm.
Proof. pose proof sf_sound as H;rewrite sf_bound_count in H;exact H. Qed.
