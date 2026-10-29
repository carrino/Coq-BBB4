From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn15PairCounter Require Import PairCounter.
Import ListNotations.

Example blank_is_main : c0=bp_main 0 0.
Proof. reflexivity. Qed.
Example initial_empty_block : csteps bp_tm 5(bp_main 0 0)=Some(bp_main 1 0).
Proof. reflexivity. Qed.
Example first_overflow : csteps bp_tm 11(bp_main 1 0)=Some(bp_main 1 1).
Proof. reflexivity. Qed.
Example even_prefix_overflow : csteps bp_tm 17(bp_main 2 0)=Some(bp_main 1 2).
Proof. reflexivity. Qed.
Example zero_prefix_nonempty : csteps bp_tm 12(bp_main 0 1)=Some(bp_main 2 0).
Proof. reflexivity. Qed.
Example later_nonempty : csteps bp_tm 52(bp_main 2 3)=Some(bp_main 4 2).
Proof. reflexivity. Qed.
Example left_sweep_context :
 csteps bp_tm 4(bp_back StB[S1;S3;S2;S0][S3])=
 Some(bp_back StB[S2;S0][S2;S0;S3]).
Proof. reflexivity. Qed.
Example right_sweep_context :
 csteps bp_tm 6(bp_front StA[S3;S2][S2;S0;S1])=
 Some(bp_front StA[S1;S3;S3;S2][S1]).
Proof. reflexivity. Qed.
