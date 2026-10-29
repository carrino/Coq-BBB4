From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn15ShuttleCounter Require Import ShuttleCounter.
Import ListNotations.

Example actual_entry : csteps bs_tm 16 c0=Some(bs_main 0 1 1).
Proof. reflexivity. Qed.
Example empty_first_block : csteps bs_tm 12(bs_main 0 1 1)=Some(bs_main 2 0 1).
Proof. reflexivity. Qed.
Example first_overflow : csteps bs_tm 13(bs_main 1 0 1)=Some(bs_main 0 1 2).
Proof. reflexivity. Qed.
Example zero_third_parameter : csteps bs_tm 13(bs_main 1 0 0)=Some(bs_main 0 1 1).
Proof. reflexivity. Qed.
Example later_overflow : csteps bs_tm 23(bs_main 2 0 1)=Some(bs_main 0 2 2).
Proof. reflexivity. Qed.
Example carry_context :
 csteps bs_tm 3(StA,([S0;S3;S2],S1,[S3]))=Some(StA,([S0;S2],S1,[S2;S3])).
Proof. reflexivity. Qed.
Example excluded_corner_actual_run :
 csteps bs_tm 3(bs_main 0 0 1)=Some(StA,([S3;S3;S3],S0,[])).
Proof. reflexivity. Qed.
Example excluded_corner_invalid_rule :
 csteps bs_tm 3(bs_main 0 0 1)<>Some(bs_main 0 0 2).
Proof. discriminate. Qed.
