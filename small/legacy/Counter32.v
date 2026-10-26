(** Selected binary recurrence certificates from the existing closeout. *)
From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
 EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr.
Import ListNotations.
(* Reuses theories/CloseoutTr/CBT_DX1_00.v: 0RB0LB_0RC1LB_1LA1RC_------. *)
Definition legacy32_000:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S0 DL StB)|StB,S0=>Some(mkTrans S0 DR StC)|StB,S1=>Some(mkTrans S1 DL StB)|StC,S0=>Some(mkTrans S1 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_000_recur:NeverQuasiHaltsTr legacy32_000.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197791%nat (83) (3) (1) (1) StC S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StA S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_00.v: 0RB0LC_1LA1RB_0RB1LC_------. *)
Definition legacy32_001:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S0 DL StC)|StB,S0=>Some(mkTrans S1 DL StA)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S0 DR StB)|StC,S1=>Some(mkTrans S1 DL StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_001_recur:NeverQuasiHaltsTr legacy32_001.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197624%nat (83) (3) (1) (1) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StA S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_01.v: 0RB1LA_1LC1RB_0RA0LA_------. *)
Definition legacy32_002:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S0 DR StA)|StC,S1=>Some(mkTrans S0 DL StA)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_002_recur:NeverQuasiHaltsTr legacy32_002.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197790%nat (83) (3) (1) (1) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_01.v: 0RB1LA_1LC1RB_0RB0LA_------. *)
Definition legacy32_003:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S0 DR StB)|StC,S1=>Some(mkTrans S0 DL StA)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_003_recur:NeverQuasiHaltsTr legacy32_003.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197624%nat (83) (3) (1) (1) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_01.v: 0RB1LA_1LC1RB_1LA0LA_------. *)
Definition legacy32_004:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S1 DL StA)|StC,S1=>Some(mkTrans S0 DL StA)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_004_recur:NeverQuasiHaltsTr legacy32_004.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190321%nat (104) (3) (1) (2) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_02.v: 0RB1LA_1LC1RB_1RA0LA_------. *)
Definition legacy32_005:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S1 DR StA)|StC,S1=>Some(mkTrans S0 DL StA)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_005_recur:NeverQuasiHaltsTr legacy32_005.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190425%nat (104) (3) (1) (2) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_02.v: 0RB1LA_1LC1RB_1RB0LA_------. *)
Definition legacy32_006:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S0 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S1 DR StB)|StC,S1=>Some(mkTrans S0 DL StA)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_006_recur:NeverQuasiHaltsTr legacy32_006.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190322%nat (103) (2) (1) (2) StA S0 [] [] [(1%nat, (1), (0)); (0%nat, (0), (1)); (1%nat, (0), (1))] [mkBRuleP StA S0 [] [(1%nat, BV (-1) (2)); (0%nat, BC (1)); (1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_04.v: 1RB0LB_0RC1LB_1LA1RC_------. *)
Definition legacy32_007:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S0 DL StB)|StB,S0=>Some(mkTrans S0 DR StC)|StB,S1=>Some(mkTrans S1 DL StB)|StC,S0=>Some(mkTrans S1 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_007_recur:NeverQuasiHaltsTr legacy32_007.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 195936%nat (105) (3) (1) (2) StC S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StA S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_05.v: 1RB0LC_1LA1RB_0RB1LC_------. *)
Definition legacy32_008:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S0 DL StC)|StB,S0=>Some(mkTrans S1 DL StA)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S0 DR StB)|StC,S1=>Some(mkTrans S1 DL StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_008_recur:NeverQuasiHaltsTr legacy32_008.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 195729%nat (105) (3) (1) (2) StB S0 [] [(1%nat, (1), (0))] [] [mkBRuleP StA S1 [(1%nat, BV (-1) (2))] [(1%nat, BV (1) (1))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_SP_09.v: 1RB0LC_1LC0RA_1LA1LB_------. *)
Definition legacy32_009:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S0 DL StC)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S0 DR StA)|StC,S0=>Some(mkTrans S1 DL StA)|StC,S1=>Some(mkTrans S1 DL StB)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_009_recur:NeverQuasiHaltsTr legacy32_009.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 85865%nat (253) (5) (2) (3) StA S0 [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])] [] [(1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (2), (0))] [mkBRuleP StB S1 [(3%nat, BV (2) (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3))] (false, true)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_SP_10.v: 1RB0LC_1RC1RA_1LA0RB_------. *)
Definition legacy32_010:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S0 DL StC)|StB,S0=>Some(mkTrans S1 DR StC)|StB,S1=>Some(mkTrans S1 DR StA)|StC,S0=>Some(mkTrans S1 DL StA)|StC,S1=>Some(mkTrans S0 DR StB)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_010_recur:NeverQuasiHaltsTr legacy32_010.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 194319%nat (382) (6) (2) (2) StC S0 [(2%nat, [S1; S0]);
   (3%nat, [S0; S1])] [(1%nat, (2), (0))] [] [mkBRuleP StA S1 [(1%nat, BV (-2) (3))] [(2%nat, BV (2) (1)); (1%nat, BC (1))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_06.v: 1RB0RB_0LC1RB_1RA1LC_------. *)
Definition legacy32_011:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S0 DR StB)|StB,S0=>Some(mkTrans S0 DL StC)|StB,S1=>Some(mkTrans S1 DR StB)|StC,S0=>Some(mkTrans S1 DR StA)|StC,S1=>Some(mkTrans S1 DL StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_011_recur:NeverQuasiHaltsTr legacy32_011.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 195835%nat (105) (3) (1) (2) StC S0 [] [] [(1%nat, (1), (0))] [mkBRuleP StA S1 [(1%nat, BV (1) (1))] [(1%nat, BV (-1) (2))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_07.v: 1RB1LA_0LA0RC_0LA1RC_------. *)
Definition legacy32_012:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S0 DL StA)|StB,S1=>Some(mkTrans S0 DR StC)|StC,S0=>Some(mkTrans S0 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_012_recur:NeverQuasiHaltsTr legacy32_012.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197623%nat (83) (3) (1) (1) StA S0 [] [] [(1%nat, (1), (0))] [mkBRuleP StB S1 [(1%nat, BV (1) (1))] [(1%nat, BV (-1) (2))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_08.v: 1RB1LA_0LC0RC_0LA1RC_------. *)
Definition legacy32_013:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S0 DL StC)|StB,S1=>Some(mkTrans S0 DR StC)|StC,S0=>Some(mkTrans S0 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_013_recur:NeverQuasiHaltsTr legacy32_013.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 197789%nat (83) (3) (1) (1) StA S0 [] [] [(1%nat, (1), (0))] [mkBRuleP StB S1 [(1%nat, BV (1) (1))] [(1%nat, BV (-1) (2))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_08.v: 1RB1LA_1LA0RC_0LA1RC_------. *)
Definition legacy32_014:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StA)|StB,S1=>Some(mkTrans S0 DR StC)|StC,S0=>Some(mkTrans S0 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_014_recur:NeverQuasiHaltsTr legacy32_014.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190321%nat (103) (2) (1) (2) StC S0 [] [(1%nat, (1), (0)); (0%nat, (0), (1)); (1%nat, (0), (1))] [] [mkBRuleP StC S0 [(1%nat, BV (-1) (2)); (0%nat, BC (1)); (1%nat, BV (1) (1))] [] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_08.v: 1RB1LA_1LC0RC_0LA1RC_------. *)
Definition legacy32_015:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S0 DR StC)|StC,S0=>Some(mkTrans S0 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_015_recur:NeverQuasiHaltsTr legacy32_015.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190424%nat (104) (3) (1) (2) StA S0 [] [] [(1%nat, (1), (0))] [mkBRuleP StB S1 [(1%nat, BV (1) (1))] [(1%nat, BV (-1) (2))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_DX1_10.v: 1RB1LA_1RC0RC_0LA1RC_------. *)
Definition legacy32_016:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DL StA)|StB,S0=>Some(mkTrans S1 DR StC)|StB,S1=>Some(mkTrans S0 DR StC)|StC,S0=>Some(mkTrans S0 DL StA)|StC,S1=>Some(mkTrans S1 DR StC)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_016_recur:NeverQuasiHaltsTr legacy32_016.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 190320%nat (104) (3) (1) (2) StA S0 [] [] [(1%nat, (1), (0))] [mkBRuleP StB S1 [(1%nat, BV (1) (1))] [(1%nat, BV (-1) (2))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
(* Reuses theories/CloseoutTr/CBT_SP_24.v: 1RB1RC_1LC0RA_1RA0LB_------. *)
Definition legacy32_017:TM:=fun q s=>match q,s with |StA,S0=>Some(mkTrans S1 DR StB)|StA,S1=>Some(mkTrans S1 DR StC)|StB,S0=>Some(mkTrans S1 DL StC)|StB,S1=>Some(mkTrans S0 DR StA)|StC,S0=>Some(mkTrans S1 DR StA)|StC,S1=>Some(mkTrans S0 DL StB)|StD,S0=>None|StD,S1=>None end.
Lemma legacy32_017_recur:NeverQuasiHaltsTr legacy32_017.
Proof. apply (irulesblkpfx_check_neverqhtr_sound _ (mkBIRCertP 134626%nat (318) (6) (2) (2) StB S0 [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])] [(1%nat, (2), (0))] [] [mkBRuleP StC S1 [(1%nat, BV (-2) (3))] [(3%nat, BV (2) (1)); (1%nat, BC (1))] (true, false)])%Z 200000 300000). native_compute. reflexivity. Qed.
