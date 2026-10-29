From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn34S061 Require Import Grammar.
Import ListNotations.

Example actual_blank_entry : csteps s61_tm 5 c0=Some(s61_main_O 0 O0).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_0_context : csteps s61_tm 3(s61_back StB(s61_ew E0)[S0;S2;S3])=Some(s61_front StA(s61_ne E0)[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_0 : csteps s61_tm 21(s61_main_E 0 E0)=Some(s61_main_O 1(s61_en E0)).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_1_context : csteps s61_tm 7(s61_back StB(s61_ew E1)[S0;S2;S3])=Some(s61_front StA(s61_ne E1)[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_1 : csteps s61_tm 31(s61_main_E 0 E1)=Some(s61_main_O 1(s61_en E1)).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_2_context : csteps s61_tm 17(s61_back StB(s61_ew (E2 O0))[S0;S2;S3])=Some(s61_front StA(s61_ne (E2 O0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_2 : csteps s61_tm 39(s61_main_E 0 (E2 O0))=Some(s61_main_O 1(s61_en (E2 O0))).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_3_context : csteps s61_tm 3(s61_back StB(s61_ew (E3 E0))[S0;S2;S3])=Some(s61_front StA(s61_ne (E3 E0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_3 : csteps s61_tm 19(s61_main_E 0 (E3 E0))=Some(s61_main_O 1(s61_en (E3 E0))).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_4_context : csteps s61_tm 7(s61_back StB(s61_ew (E4 E0))[S0;S2;S3])=Some(s61_front StA(s61_ne (E4 E0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_4 : csteps s61_tm 35(s61_main_E 0 (E4 E0))=Some(s61_main_O 1(s61_en (E4 E0))).
Proof. vm_compute;reflexivity. Qed.

Example e_normalizer_5_context : csteps s61_tm 3(s61_back StB(s61_ew (E5 O0))[S0;S2;S3])=Some(s61_front StA(s61_ne (E5 O0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example e_return_5 : csteps s61_tm 19(s61_main_E 0 (E5 O0))=Some(s61_main_O 1(s61_en (E5 O0))).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_0_context : csteps s61_tm 7(s61_back StB(s61_ow O0)[S0;S2;S3])=Some(s61_front StA(s61_no O0)[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_0 : csteps s61_tm 15(s61_main_O 0 O0)=Some(s61_main_E 0(s61_on O0)).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_1_context : csteps s61_tm 3(s61_back StB(s61_ow O1)[S0;S2;S3])=Some(s61_front StA(s61_no O1)[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_1 : csteps s61_tm 11(s61_main_O 0 O1)=Some(s61_main_E 0(s61_on O1)).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_2_context : csteps s61_tm 13(s61_back StB(s61_ow (O2 E0))[S0;S2;S3])=Some(s61_front StA(s61_no (O2 E0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_2 : csteps s61_tm 21(s61_main_O 0 (O2 E0))=Some(s61_main_E 0(s61_on (O2 E0))).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_3_context : csteps s61_tm 3(s61_back StB(s61_ow (O3 E0))[S0;S2;S3])=Some(s61_front StA(s61_no (O3 E0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_3 : csteps s61_tm 11(s61_main_O 0 (O3 E0))=Some(s61_main_E 0(s61_on (O3 E0))).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_4_context : csteps s61_tm 7(s61_back StB(s61_ow (O4 O0))[S0;S2;S3])=Some(s61_front StA(s61_no (O4 O0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_4 : csteps s61_tm 15(s61_main_O 0 (O4 O0))=Some(s61_main_E 0(s61_on (O4 O0))).
Proof. vm_compute;reflexivity. Qed.

Example o_normalizer_5_context : csteps s61_tm 3(s61_back StB(s61_ow (O5 O0))[S0;S2;S3])=Some(s61_front StA(s61_no (O5 O0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example o_return_5 : csteps s61_tm 11(s61_main_O 0 (O5 O0))=Some(s61_main_E 0(s61_on (O5 O0))).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_0_context : csteps s61_tm 7(s61_back StB(s61_ne E0)[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en E0))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_1_context : csteps s61_tm 13(s61_back StB(s61_ne E1)[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en E1))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_2_context : csteps s61_tm 11(s61_back StB(s61_ne (E2 O0))[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en (E2 O0)))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_3_context : csteps s61_tm 5(s61_back StB(s61_ne (E3 E0))[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en (E3 E0)))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_4_context : csteps s61_tm 17(s61_back StB(s61_ne (E4 E0))[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en (E4 E0)))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_5_context : csteps s61_tm 5(s61_back StB(s61_ne (E5 O0))[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en (E5 O0)))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example double_normalizer_6_context : csteps s61_tm 37(s61_back StB(s61_ne (E4 (E4 (E4 E0))))[S0;S2;S3])=Some(s61_front StA(s61_ow(s61_en (E4 (E4 (E4 E0)))))[S0;S2;S3]).
Proof. vm_compute;reflexivity. Qed.

Example positive_prefix_cycle_0 : csteps s61_tm 84(s61_main_O 3 O0)=Some(s61_main_O 4(s61_en(s61_on O0))).
Proof. vm_compute;reflexivity. Qed.

Example positive_prefix_cycle_1 : csteps s61_tm 92(s61_main_O 3 (O2 (E4 (E4 E0))))=Some(s61_main_O 4(s61_en(s61_on (O2 (E4 (E4 E0)))))).
Proof. vm_compute;reflexivity. Qed.

Example mismatched_parity_rejected : csteps s61_tm 15(s61_C 2(s61_ow O1))<>Some(s61_C 3(s61_ew(s61_on O1))).
Proof. vm_compute;discriminate. Qed.

Example missing_grammar_guard : csteps s61_tm 7(s61_back StB[S3][])<>Some(s61_front StA[S3;S3;S1][]).
Proof. vm_compute;discriminate. Qed.

Example frozen_A1_enters_B : s61_tm StA S1=Some(mkTrans S2 DL StB).
Proof. vm_compute;reflexivity. Qed.

Example altered_A1_is_distinct : s61_tm StA S1<>Some(mkTrans S2 DL StA).
Proof. vm_compute;discriminate. Qed.

Example frozen_B3_moves_left : s61_tm StB S3=Some(mkTrans S3 DL StB).
Proof. vm_compute;reflexivity. Qed.

Example altered_B3_is_distinct : s61_tm StB S3<>Some(mkTrans S3 DR StB).
Proof. vm_compute;discriminate. Qed.
