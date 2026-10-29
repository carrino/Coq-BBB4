From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn39S076 Require Import Core Grammar.
Import ListNotations.

Example actual_blank_entry : csteps s76_tm 234 c0=Some(s76_main 1(s76_word G1)).
Proof. vm_compute;reflexivity. Qed.

Example Q_train_0_context : csteps s76_tm 9(s76_back StB[S2;S2;S3;S0;S3](s76_T 0++[S0;S2;S1]))=Some(s76_back StB[S0;S3]([S0;S0]++s76_V 0++[S1;S1;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example Q_train_3_context : csteps s76_tm 27(s76_back StB[S2;S2;S3;S0;S3](s76_T 3++[S0;S2;S1]))=Some(s76_back StB[S0;S3]([S0;S0]++s76_V 3++[S1;S1;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example read_gate_0_context : csteps s76_tm 34(s76_main 0[S2;S1])=Some(s76_front StB(s76_support 0)[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example zero_gate_0_context : csteps s76_tm 31(s76_back StB(s76_support 0)[S0;S2;S1])=Some(s76_main 1[S1;S1;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example read_gate_3_context : csteps s76_tm 43(s76_main 3[S2;S1])=Some(s76_front StB(s76_support 3)[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example zero_gate_3_context : csteps s76_tm 58(s76_back StB(s76_support 3)[S0;S2;S1])=Some(s76_main 4[S1;S1;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example positive_gate_1_0 : csteps s76_tm 40(s76_back StB(s76_support 1)(s76_T 0++[S0;S2;S1]))=Some(s76_main 2(s76_V 0++[S1;S1;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example positive_gate_3_2 : csteps s76_tm 70(s76_back StB(s76_support 3)(s76_T 2++[S0;S2;S1]))=Some(s76_main 4(s76_V 2++[S1;S1;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_0_context : csteps s76_tm 3(s76_front StB[S0;S3](s76_word G0))=Some(s76_back StB[S0;S3](s76_T 0++S0::[S1;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_0_return : csteps s76_tm 80(s76_main 1(s76_word G0))=Some(s76_main 2(s76_word(s76_next G0))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_1_context : csteps s76_tm 19(s76_front StB[S0;S3](s76_word G1))=Some(s76_back StB[S0;S3](s76_T 1++S0::[S0;S1;S1;S1;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_1_return : csteps s76_tm 102(s76_main 1(s76_word G1))=Some(s76_main 2(s76_word(s76_next G1))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_2_context : csteps s76_tm 3(s76_front StB[S0;S3](s76_word G2))=Some(s76_back StB[S0;S3](s76_T 0++S0::[S1;S1;S1;S0;S1;S1;S1;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_2_return : csteps s76_tm 80(s76_main 1(s76_word G2))=Some(s76_main 2(s76_word(s76_next G2))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_3_context : csteps s76_tm 11(s76_front StB[S0;S3](s76_word G3))=Some(s76_back StB[S0;S3](s76_T 2++S0::[S1;S1;S1;S1;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_3_return : csteps s76_tm 100(s76_main 1(s76_word G3))=Some(s76_main 2(s76_word(s76_next G3))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_4_context : csteps s76_tm 3(s76_front StB[S0;S3](s76_word G4))=Some(s76_back StB[S0;S3](s76_T 0++S0::[S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_4_return : csteps s76_tm 80(s76_main 1(s76_word G4))=Some(s76_main 2(s76_word(s76_next G4))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_5_context : csteps s76_tm 59(s76_front StB[S0;S3](s76_word G5))=Some(s76_back StB[S0;S3](s76_T 1++S0::[S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_5_return : csteps s76_tm 142(s76_main 1(s76_word G5))=Some(s76_main 2(s76_word(s76_next G5))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_6_context : csteps s76_tm 3(s76_front StB[S0;S3](s76_word (W0 0 G0)))=Some(s76_back StB[S0;S3](s76_T 0++S0::[S1;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_6_return : csteps s76_tm 80(s76_main 1(s76_word (W0 0 G0)))=Some(s76_main 2(s76_word(s76_next (W0 0 G0)))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_7_context : csteps s76_tm 11(s76_front StB[S0;S3](s76_word (W1 0 G0)))=Some(s76_back StB[S0;S3](s76_T 2++S0::[S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_7_return : csteps s76_tm 100(s76_main 1(s76_word (W1 0 G0)))=Some(s76_main 2(s76_word(s76_next (W1 0 G0)))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_8_context : csteps s76_tm 3(s76_front StB[S0;S3](s76_word (W2 0 G0)))=Some(s76_back StB[S0;S3](s76_T 0++S0::[S1;S1;S0;S1;S1;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_8_return : csteps s76_tm 80(s76_main 1(s76_word (W2 0 G0)))=Some(s76_main 2(s76_word(s76_next (W2 0 G0)))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_9_context : csteps s76_tm 41(s76_front StB[S0;S3](s76_word (W3 0 G0)))=Some(s76_back StB[S0;S3](s76_T 1++S0::[S0;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_9_return : csteps s76_tm 124(s76_main 1(s76_word (W3 0 G0)))=Some(s76_main 2(s76_word(s76_next (W3 0 G0)))).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_tree_10_context : csteps s76_tm 183(s76_front StB[S0;S3](s76_word (W3 2 (W3 1 G5))))=Some(s76_back StB[S0;S3](s76_T 1++S0::[S0;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S0;S1;S1;S0;S1;S0;S1;S1;S0;S1;S1;S0;S1;S0;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_tree_10_return : csteps s76_tm 278(s76_main 2(s76_word (W3 2 (W3 1 G5))))=Some(s76_main 3(s76_word(s76_next (W3 2 (W3 1 G5))))).
Proof. vm_compute;reflexivity. Qed.

Example unrestricted_word_enters_B_blank : csteps s76_tm 51(StA,([S3;S2;S2;S3;S1;S3;S2],S0,[]))=Some(StB,([S2;S3;S2;S3;S2;S3;S2;S2;S3;S1;S3;S2],S0,[])).
Proof. vm_compute;reflexivity. Qed.

Example missing_G_support_rejected : csteps s76_tm 31(s76_back StB[][S0;S1])<>Some(s76_main 1[S1;S1;S1]).
Proof. vm_compute;discriminate. Qed.

Example frozen_A3_enters_B : s76_tm StA S3=Some(mkTrans S2 DL StB).
Proof. vm_compute;reflexivity. Qed.

Example altered_A3_is_distinct : s76_tm StA S3<>Some(mkTrans S2 DL StA).
Proof. vm_compute;discriminate. Qed.

Example frozen_B3_moves_left : s76_tm StB S3=Some(mkTrans S0 DL StB).
Proof. vm_compute;reflexivity. Qed.

Example altered_B3_is_distinct : s76_tm StB S3<>Some(mkTrans S0 DR StB).
Proof. vm_compute;discriminate. Qed.
