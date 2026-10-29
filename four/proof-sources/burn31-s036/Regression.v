From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn31S036 Require Import WordCycle.
Import ListNotations.

Example actual_blank_entry : csteps s36_tm 2758 c0=Some(s36_main 8 s36_entry_suffix).
Proof. vm_compute;reflexivity. Qed.

Example main_0_context_return : csteps s36_tm 838(s36_main 0[S3;S2;S1])=Some(s36_main 3(s36_W++[S3;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_1_context_return : csteps s36_tm 968(s36_main 1[S3;S2;S1])=Some(s36_main 4(s36_W++[S3;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example main_2_context_return : csteps s36_tm 1098(s36_main 2[S3;S2;S1])=Some(s36_main 5(s36_W++[S3;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example A_gate_0_context : csteps s36_tm 2(s36_back StA(s36_support 0)[S3;S2;S1])=Some(s36_boundary 0[S2;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example A_gate_3_context : csteps s36_tm 14(s36_back StA(s36_support 3)[S3;S2;S1])=Some(s36_boundary 3[S2;S2;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example B_gate_0_context : csteps s36_tm 2(s36_back StB(s36_support 0)[S3;S2;S1])=Some(s36_boundary 0[S2;S3;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example B_gate_3_context : csteps s36_tm 14(s36_back StB(s36_support 3)[S3;S2;S1])=Some(s36_boundary 3[S2;S3;S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example right_scan_context : csteps s36_tm 18(s36_front StA[S3;S0](s36_P 3++[S2;S1]))=Some(s36_front StA(s36_Q 3++[S3;S0])[S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example left_scan_context : csteps s36_tm 12(s36_back StB(s36_Q 3++[S0;S3])[S2;S1])=Some(s36_back StB[S0;S3](s36_E 3++[S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example phase_0_context : csteps s36_tm 10(s36_phase 0 0[S3;S2;S1])=Some(s36_phase 1 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_1_context : csteps s36_tm 10(s36_phase 1 0[S3;S2;S1])=Some(s36_phase 2 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_2_context : csteps s36_tm 36(s36_phase 2 0[S3;S2;S1])=Some(s36_phase 3 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_3_context : csteps s36_tm 120(s36_phase 3 0[S3;S2;S1])=Some(s36_phase 4 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_4_context : csteps s36_tm 136(s36_phase 4 0[S3;S2;S1])=Some(s36_phase 5 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_5_context : csteps s36_tm 20(s36_phase 5 0[S3;S2;S1])=Some(s36_phase 6 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_6_context : csteps s36_tm 20(s36_phase 6 0[S3;S2;S1])=Some(s36_phase 7 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_7_context : csteps s36_tm 46(s36_phase 7 0[S3;S2;S1])=Some(s36_phase 8 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_8_context : csteps s36_tm 104(s36_phase 8 0[S3;S2;S1])=Some(s36_phase 9 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_9_context : csteps s36_tm 30(s36_phase 9 0[S3;S2;S1])=Some(s36_phase 10 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_10_context : csteps s36_tm 30(s36_phase 10 0[S3;S2;S1])=Some(s36_phase 11 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_11_context : csteps s36_tm 56(s36_phase 11 0[S3;S2;S1])=Some(s36_phase 12 0[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.

Example phase_12_context : csteps s36_tm 220(s36_phase 12 0[S3;S2;S1])=Some(s36_main 3(s36_W++[S3;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example last_phase_positive_context : csteps s36_tm 240(s36_phase 12 2[S3;S2;S1])=Some(s36_main 5(s36_W++[S3;S2;S1])).
Proof. vm_compute;reflexivity. Qed.

Example missing_A_support : csteps s36_tm 2(s36_back StA[][S3;S2;S1])<>Some(s36_boundary 0[S2;S2;S3;S2;S1]).
Proof. vm_compute;discriminate. Qed.

Example missing_B_support : csteps s36_tm 2(s36_back StB[][S3;S2;S1])<>Some(s36_boundary 0[S2;S3;S3;S2;S1]).
Proof. vm_compute;discriminate. Qed.

Example frozen_A2_enters_B : s36_tm StA S2=Some(mkTrans S2 DR StB).
Proof. vm_compute;reflexivity. Qed.

Example altered_A2_is_distinct : s36_tm StA S2<>Some(mkTrans S2 DR StA).
Proof. vm_compute;discriminate. Qed.

Example frozen_B1_enters_A : s36_tm StB S1=Some(mkTrans S3 DL StA).
Proof. vm_compute;reflexivity. Qed.

Example altered_B1_is_distinct : s36_tm StB S1<>Some(mkTrans S3 DL StB).
Proof. vm_compute;discriminate. Qed.
