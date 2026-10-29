From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn27S040WordCycle Require Import WordCycle.
Import ListNotations.

Example actual_blank_entry : csteps s40_tm 3 c0=Some(s40_main 0).
Proof. vm_compute;reflexivity. Qed.

Example main_zero_return : csteps s40_tm 577(s40_main 0)=Some(s40_main 1).
Proof. vm_compute;reflexivity. Qed.

Example main_one_return : csteps s40_tm 1633(s40_main 1)=Some(s40_main 2).
Proof. vm_compute;reflexivity. Qed.

Example main_two_return : csteps s40_tm 2689(s40_main 2)=Some(s40_main 3).
Proof. vm_compute;reflexivity. Qed.

Example B_gate_zero_context : csteps s40_tm 1(s40_front StB[S0;S3][S1;S2;S1])=Some(s40_front StA[S2;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example B_gate_positive_context : csteps s40_tm 61(s40_front StB[S0;S3](s40_E 2++[S1;S2;S1]))=Some(s40_front StA(s40_word 2++[S2;S0;S3])[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example A_gate_zero_context : csteps s40_tm 3(s40_front StA[S2;S0;S3][S1;S2;S1])=Some(s40_front StA[S3;S3;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example A_gate_positive_context : csteps s40_tm 63(s40_front StA[S2;S0;S3](s40_E 2++[S1;S2;S1]))=Some(s40_front StA(s40_word 2++[S3;S3;S0;S3])[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example left_scan_context : csteps s40_tm 132(s40_back StB(s40_word 2++[S1;S2])[S0;S3])=Some(s40_back StB[S1;S2](s40_E 2++[S0;S3])).
Proof. vm_compute;reflexivity. Qed.

Example right_scan_context : csteps s40_tm 60(StA,([S0;S3],S2,s40_H 2++[S2;S1]))=Some(StA,(s40_V 2++[S0;S3],S2,[S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example row0_zero_context : csteps s40_tm 5(s40_stage 0 0[S2;S1])=Some(s40_front StA[S2;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row1_zero_context : csteps s40_tm 11(s40_stage 1 0[S2;S1])=Some(s40_front StA[S2;S0;S3;S3;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row2_zero_context : csteps s40_tm 31(s40_stage 2 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S2;S2;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row3_zero_context : csteps s40_tm 43(s40_stage 3 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S3;S2;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row4_zero_context : csteps s40_tm 51(s40_stage 4 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S3;S3;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row5_zero_context : csteps s40_tm 81(s40_stage 5 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S2;S3;S3;S0;S2;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row6_zero_context : csteps s40_tm 47(s40_stage 6 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S0;S3;S3;S3;S0;S2;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row7_zero_context : csteps s40_tm 69(s40_stage 7 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S0;S2;S0;S3;S3;S0;S3;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row8_zero_context : csteps s40_tm 87(s40_stage 8 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S0;S2;S0;S2;S2;S3;S3;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row9_zero_context : csteps s40_tm 55(s40_stage 9 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S0;S2;S0;S2;S0;S3;S3;S3;S0;S3][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example row10_zero_context : csteps s40_tm 97(s40_stage 10 0[S2;S1])=Some(s40_front StA[S3;S3;S2;S3;S3;S0;S2;S0;S2;S0;S2;S0;S3;S3;S2;S3;S3;S0;S2;S2][S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example last_row_positive_context : csteps s40_tm 289(s40_stage 10 2[S3;S1])=Some(s40_front StA(s40_word 3++[S2;S2])[S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example missing_A_support : csteps s40_tm 3(s40_front StA[S0][S1])<>Some(s40_front StA[S3;S3][]).
Proof. vm_compute;discriminate. Qed.

Example missing_B_tag : csteps s40_tm 1(s40_front StB[][S0])<>Some(s40_front StA[S2][]).
Proof. vm_compute;discriminate. Qed.

Example altered_A3_is_distinct : s40_tm StA S3<>Some(mkTrans S0 DR StA).
Proof. vm_compute;discriminate. Qed.

Example altered_B3_is_distinct : s40_tm StB S3<>Some(mkTrans S1 DL StA).
Proof. vm_compute;discriminate. Qed.

Example frozen_A3_enters_B : s40_tm StA S3=Some(mkTrans S0 DR StB).
Proof. vm_compute;reflexivity. Qed.
Example frozen_B3_stays_B : s40_tm StB S3=Some(mkTrans S1 DL StB).
Proof. vm_compute;reflexivity. Qed.
