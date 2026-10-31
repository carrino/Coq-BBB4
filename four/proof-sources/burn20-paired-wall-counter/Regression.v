From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20PairedWallCounter Require Import PairedWallCounter.
Import ListNotations.
Example actual_blank_entry : csteps wc_tm 149 c0=Some(wc_main 0).
Proof. vm_compute;reflexivity. Qed.
Example odd_phase_boundary : csteps wc_tm 63(wc_stage 3 1[])=Some(wc_stage 3 2[]).
Proof. vm_compute;reflexivity. Qed.
Example even_phase_boundary : csteps wc_tm 285(wc_stage 3 2[])=Some(wc_stage 4 4[]).
Proof. vm_compute;reflexivity. Qed.
Example left_scan_context : csteps wc_tm 40(wc_X 5[S3;S0])=Some(wc_X 1(wc_W 2++[S3;S0])).
Proof. vm_compute;reflexivity. Qed.
Example right32_scan_context : csteps wc_tm 64(wc_Y 0(S3::S2::(wc_W 2++[S1])))=
 Some(wc_Y 4[S3;S2;S1]).
Proof. vm_compute;reflexivity. Qed.
Example right58_scan_context : csteps wc_tm 58(wc_Y 1(S3::S2::S1::S1::S1::(wc_W 1++[S2])))=
 Some(wc_Y 3[S3;S2;S1;S1;S1;S2]).
Proof. vm_compute;reflexivity. Qed.
Example odd_turn_context : csteps wc_tm 38(wc_X 1[S2;S3])=Some(wc_Y 0[S3;S2;S2;S3]).
Proof. vm_compute;reflexivity. Qed.
Example even_turn_context : csteps wc_tm 35(wc_X 0[S3;S2;S1;S1;S0;S3])=
 Some(wc_Y 0[S3;S2;S1;S1;S1;S0;S3]).
Proof. vm_compute;reflexivity. Qed.
Example odd_finish_nonblank_context : csteps wc_tm 23(wc_Y 1[S3;S2;S3;S1;S2;S1])=
 Some(wc_front StA(S1::S1::S1::wc_left 3)[S2;S1]).
Proof. vm_compute;reflexivity. Qed.
Example even_finish_nonblank_context : csteps wc_tm 114(wc_Y 0[S3;S2;S1;S1;S1;S3;S2;S3;S2;S2])=
 Some(wc_front StA(S1::S1::S1::S1::wc_left 4)[S2]).
Proof. vm_compute;reflexivity. Qed.
Example four_phase_reads_outer_context : csteps wc_tm 21(wc_stage 4 0[S1])=
 Some(wc_front StA(S1::S1::S1::wc_left 1)[S1]).
Proof. vm_compute;reflexivity. Qed.
Example missing_guard_invalidates_R32 : csteps wc_tm 32(StA,([S1;S1;S1],S1,[S3;S2;S3;S2;S1;S1]))<>
 Some(StA,([S1;S1;S3;S0;S3;S0;S1],S1,[S3;S2])).
Proof. vm_compute;discriminate. Qed.
Example frozen_A3_stays_A : wc_tm StA S3=Some(mkTrans S1 DR StA).
Proof. vm_compute;reflexivity. Qed.
Example altered_A3_is_distinct : wc_tm StA S3<>Some(mkTrans S1 DR StB).
Proof. vm_compute;discriminate. Qed.
