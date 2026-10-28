From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn26S010Crossing Require Import WordCycle.
Import ListNotations.
Example actual_blank_entry : csteps s10_tm 2079 c0=Some(s10_main 8).
Proof. vm_compute;reflexivity. Qed.
Example smallest_main_return : csteps s10_tm 2076(s10_main 0)=Some(s10_main 8).
Proof. vm_compute;reflexivity. Qed.
Example nonmultiple_main_return : csteps s10_tm 2524(s10_main 1)=Some(s10_main 9).
Proof. vm_compute;reflexivity. Qed.
Example cycle_preserves_outer_context : csteps s10_tm 2972(s10_phase 0 2[S2;S3])=
 Some(s10_phase 0 10[S2;S3]).
Proof. vm_compute;reflexivity. Qed.
Example B_gate_zero_nonblank_context : csteps s10_tm 6(s10_back StB(s10_tail 0)[S2;S1])=
 Some(StB,(S1::s10_tail 0,S0,[S2;S1])).
Proof. vm_compute;reflexivity. Qed.
Example B_gate_nonzero_context : csteps s10_tm 38(s10_back StB(s10_tail 2)[S2;S0;S1])=
 Some(StB,(S1::s10_tail 2,S0,[S2;S0;S1])).
Proof. vm_compute;reflexivity. Qed.
Example A_gate_zero_reads_context : csteps s10_tm 7(s10_back StA(s10_tail 0)[S3;S1])=
 Some(s10_front StA(S1::S1::s10_tail 0)[S3;S1]).
Proof. vm_compute;reflexivity. Qed.
Example A_gate_nonzero_context : csteps s10_tm 55(s10_back StA(s10_tail 3)[S2;S1])=
 Some(s10_front StA(S1::S1::s10_tail 3)[S2;S1]).
Proof. vm_compute;reflexivity. Qed.
Example left_scan_context : csteps s10_tm 18(s10_back StB(s10_word 2++[S2;S1])[S0;S3])=
 Some(s10_back StB[S2;S1](s10_E 2++[S0;S3])).
Proof. vm_compute;reflexivity. Qed.
Example right_scan_context : csteps s10_tm 14(StB,([S2;S1],S0,s10_E 2++[S3;S2]))=
 Some(StB,(s10_V 2++[S2;S1],S0,[S3;S2])).
Proof. vm_compute;reflexivity. Qed.
Example phase0_context : csteps s10_tm 9(s10_phase 0 0[S3;S1])=Some(s10_phase 1 0[S3;S1]).
Proof. vm_compute;reflexivity. Qed.
Example phase2_A_gate_boundary : csteps s10_tm 25(s10_phase 2 0[S1;S2])=Some(s10_phase 3 0[S1;S2]).
Proof. vm_compute;reflexivity. Qed.
Example phase4_five_gate_context : csteps s10_tm 245(s10_phase 4 1[S2;S3])=Some(s10_phase 5 3[S2;S3]).
Proof. vm_compute;reflexivity. Qed.
Example phase5_fifteen_gate_zero : csteps s10_tm 707(s10_phase 5 0[S2;S1])=Some(s10_phase 6 4[S2;S1]).
Proof. vm_compute;reflexivity. Qed.
Example phase5_fifteen_gate_positive : csteps s10_tm 1427(s10_phase 5 3[])=Some(s10_phase 6 7[]).
Proof. vm_compute;reflexivity. Qed.
Example phase6_boundary : csteps s10_tm 21(s10_phase 6 0[S3])=Some(s10_phase 7 0[S3]).
Proof. vm_compute;reflexivity. Qed.
Example phase7_boundary : csteps s10_tm 6(s10_phase 7 0[S3])=Some(s10_phase 8 0[S3]).
Proof. vm_compute;reflexivity. Qed.
Example phase8_boundary : csteps s10_tm 17(s10_phase 8 0[S1;S3])=Some(s10_phase 0 1[S1;S3]).
Proof. vm_compute;reflexivity. Qed.
Example missing_wall_excludes_gate : csteps s10_tm 6(s10_back StB[][])<>Some(StB,([S1],S0,[])).
Proof. vm_compute;discriminate. Qed.
Example frozen_A3_stays_A : s10_tm StA S3=Some(mkTrans S2 DL StA).
Proof. vm_compute;reflexivity. Qed.
Example altered_A3_is_distinct : s10_tm StA S3<>Some(mkTrans S2 DL StB).
Proof. vm_compute;discriminate. Qed.
Example frozen_B3_enters_A : s10_tm StB S3=Some(mkTrans S0 DL StA).
Proof. vm_compute;reflexivity. Qed.
Example altered_B3_is_distinct : s10_tm StB S3<>Some(mkTrans S0 DL StB).
Proof. vm_compute;discriminate. Qed.
