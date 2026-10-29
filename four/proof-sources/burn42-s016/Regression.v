From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn42S016 Require Import Normalizer S016.
Import ListNotations.

Example actual_blank_entry : csteps b16_tm 56 c0=Some(b16_C[ba;bb]).
Proof. vm_compute;reflexivity. Qed.

Example program_CA_context : csteps b16_tm 120(bn_cut[S1;S3;S3;S1;S2;S3;S2;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S1;S3;S3;S0;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_CD_context : csteps b16_tm 183(bn_cut[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S3;S3;S0;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_toK_context : csteps b16_tm 3(bn_at StA[S3;S2;S1]S3[S1;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S3;S3;S0;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_KA_context : csteps b16_tm 29(bn_back StB[S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S3;S3;S0;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_KB_context : csteps b16_tm 37(bn_back StB[S0;S1;S2;S3;S2;S1][S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_KD_context : csteps b16_tm 98(bn_back StB[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S0;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_toM_context : csteps b16_tm 9(bn_at StA[S3;S2;S1]S3[S3;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S0;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_MB_context : csteps b16_tm 69(bn_back StB[S0;S1;S2;S3;S2;S1][S0;S3;S0;S3;S1;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3]).
Proof. vm_compute;reflexivity. Qed.

Example program_MD_context : csteps b16_tm 94(bn_back StB[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S0;S3;S1;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_HA_context : csteps b16_tm 29(bn_back StB[S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S1;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_HB_context : csteps b16_tm 10(bn_back StB[S0;S1;S2;S3;S2;S1][S0;S3;S1;S3;S1])=Some(bn_cut[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_HD_context : csteps b16_tm 46(bn_back StB[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S1;S3;S1])=Some(bn_cut[S1;S3;S3;S1;S2;S1;S3;S3;S1;S2;S3;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_LB_context : csteps b16_tm 14(bn_back StB[S0;S1;S2;S3;S2;S1][S0;S3;S0;S3;S1])=Some(bn_cut[S1;S3;S3;S1;S2;S3;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_LD_context : csteps b16_tm 94(bn_back StB[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1][S0;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_C12D_context : csteps b16_tm 43(bn_cut[S1;S2;S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1])=Some(bn_cut[S0;S1;S2;S1;S3;S3;S1;S2;S3;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_oneD_context : csteps b16_tm 42(bn_at StA[S1;S3;S3;S1;S3;S3;S1;S2;S3;S2;S1]S3[S1])=Some(bn_cut[S1;S2;S1;S3;S3;S1;S2;S3;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_RC81_context : csteps b16_tm 81(bn_at StA[S3;S2;S1]S3[S3;S1;S3;S3;S3;S3;S0;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3]).
Proof. vm_compute;reflexivity. Qed.

Example program_KD115_context : csteps b16_tm 115(bn_at StA[S3;S2;S1]S3[S3;S1;S3;S3;S0;S3;S1;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_KD6_context : csteps b16_tm 6(bn_at StA[S3;S2;S1]S3[S3;S1;S3;S3;S1])=Some(bn_cut[S0;S1;S2;S0;S1;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example program_MA5_context : csteps b16_tm 5(bn_at StA[S3;S2;S1]S3[S3;S0;S3;S1;S3;S1])=Some(bn_back StB[S3;S2;S1][S0;S3;S1;S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_branch_0_context : csteps b16_tm 30(bn_back StB(bn_enc[]++[S3])(S0::bn_Fword++[S2;S1]))=Some(bn_at StA(bn_enc(bn_F[])++[S3])S3[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_branch_1_context : csteps b16_tm 68(bn_back StB(bn_enc[ba]++[S3])(S0::bn_Fword++[S2;S1]))=Some(bn_at StA(bn_enc(bn_F[ba])++[S3])S3[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_branch_2_context : csteps b16_tm 10(bn_back StB(bn_enc[bb]++[S3])(S0::bn_Fword++[S2;S1]))=Some(bn_at StA(bn_enc(bn_F[bb])++[S3])S3[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_branch_3_context : csteps b16_tm 56(bn_back StB(bn_enc[bc]++[S3])(S0::bn_Fword++[S2;S1]))=Some(bn_at StA(bn_enc(bn_F[bc])++[S3])S3[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example normalizer_branch_4_context : csteps b16_tm 46(bn_back StB(bn_enc[bd]++[S3])(S0::bn_Fword++[S2;S1]))=Some(bn_at StA(bn_enc(bn_F[bd])++[S3])S3[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_0_0_return : csteps b16_tm 552(b16_C[ba])=Some(b16_C[bd;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_0_1_return : csteps b16_tm 856(b16_C[ba;ba])=Some(b16_C[ba;bd;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_0_2_return : csteps b16_tm 454(b16_C[ba;bb])=Some(b16_C[ba;bc;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_0_3_return : csteps b16_tm 273(b16_C[ba;bc])=Some(b16_C[ba;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_0_4_return : csteps b16_tm 782(b16_C[ba;bd])=Some(b16_C[ba;bb;ba;ba;ba;bc]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_3_0_return : csteps b16_tm 740(b16_C[bd])=Some(b16_C[ba;ba;bd;ba;bb]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_3_1_return : csteps b16_tm 930(b16_C[bd;ba])=Some(b16_C[ba;ba;ba;bd;ba;bb]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_3_2_return : csteps b16_tm 680(b16_C[bd;bb])=Some(b16_C[ba;ba;ba;bc;ba;bb]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_3_3_return : csteps b16_tm 632(b16_C[bd;bc])=Some(b16_C[ba;bd;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example guarded_3_4_return : csteps b16_tm 896(b16_C[bd;bd])=Some(b16_C[ba;ba;ba;bb;ba;bd]).
Proof. vm_compute;reflexivity. Qed.

Example KD_wrong_digit_rejected : csteps b16_tm 98(bn_back StB(bn_code bd++[S3])[S0;S3;S3;S3;S0;S3;S1])<>Some(bn_back StB[S3](S0::bn_Fword++[S3;S1;S3;S1;S0;S3;S1;S3;S1])).
Proof. vm_compute;discriminate. Qed.

Example missing_terminal_marker_rejected : csteps b16_tm 30(bn_back StB[](S0::bn_Fword++[S3;S1]))<>Some(bn_at StA(bn_enc[ba;bb]++[S3])S3[S3;S1]).
Proof. vm_compute;discriminate. Qed.

Example frozen_B2_writes_one_right : b16_tm StB S2=Some(mkTrans S1 DR StA).
Proof. vm_compute;reflexivity. Qed.

Example wrong_zero_B2_rejected : b16_tm StB S2<>Some(mkTrans S0 DR StA).
Proof. vm_compute;discriminate. Qed.

Example wrong_left_B2_rejected : b16_tm StB S2<>Some(mkTrans S0 DL StB).
Proof. vm_compute;discriminate. Qed.
