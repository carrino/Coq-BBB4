From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20PairAccumulator Require Import PairAccumulator.
Import ListNotations.
Example actual_blank_entry : csteps pa_tm 68 c0=Some(pa_main 3 1).
Proof. vm_compute;reflexivity. Qed.
Example smallest_positive_main : csteps pa_tm 51(pa_main 0 0)=Some(pa_main 3 1).
Proof. vm_compute;reflexivity. Qed.
Example actual_first_return : csteps pa_tm 265(pa_main 3 1)=Some(pa_main 6 5).
Proof. vm_compute;reflexivity. Qed.
Example actual_second_return : csteps pa_tm 827(pa_main 6 5)=Some(pa_main 9 12).
Proof. vm_compute;reflexivity. Qed.
Example support_arbitrary_context : csteps pa_tm 6
 (pa_front StA[S2;S1;S0;S3][S2;S3;S1;S0])=
 Some(pa_front StA[S2;S1;S1;S2;S0;S3][S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example restore_one_pair_nonblank : csteps pa_tm 13
 (pa_back StB(pa_P 1)[S0;S3;S1])=
 Some(pa_front StA(S2::S1::pa_P 1)[S0;S3;S1]).
Proof. vm_compute;reflexivity. Qed.
Example restore_three_pairs_nonblank : csteps pa_tm 29
 (pa_back StB(pa_P 3)[S2;S1;S0])=
 Some(pa_front StA(S2::S1::pa_P 3)[S2;S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example erase_empty_left_run : csteps pa_tm 3
 (pa_front StA[S1;S3;S0][S2;S1;S3])=
 Some(pa_front StB[S1;S2;S3;S0][S1;S3]).
Proof. vm_compute;reflexivity. Qed.
Example increment_tag2_nonblank : csteps pa_tm 40
 (pa_front StA(S2::S1::pa_P 1)[S3;S3;S3;S2;S2;S0;S1])=
 Some(pa_front StA(S2::S1::pa_P 2)[S3;S3;S3;S3;S2;S0;S1]).
Proof. vm_compute;reflexivity. Qed.
Example increment_tag1_nonblank : csteps pa_tm 48
 (pa_front StA(S2::S1::pa_P 2)[S3;S3;S3;S2;S1;S2;S0])=
 Some(pa_front StA(S2::S1::pa_P 3)[S3;S3;S3;S3;S3;S2;S0]).
Proof. vm_compute;reflexivity. Qed.
Example finish_smallest_boundary : csteps pa_tm 35(pa_G 1 0 1)=Some(pa_stage 4 2[]).
Proof. vm_compute;reflexivity. Qed.
Example loop_smallest_boundary : csteps pa_tm 32(pa_G 1 0 2)=Some(pa_G 2 1 1).
Proof. vm_compute;reflexivity. Qed.
Example start_zero_leading_run : csteps pa_tm 15(pa_stage 0 1[S3;S1])=
 Some(pa_front StA(S2::S1::pa_P 1)[S3;S1;S3;S1]).
Proof. vm_compute;reflexivity. Qed.
Example zero_leading_run_excludes_main_return : csteps pa_tm 17(pa_stage 0 1[])<>
 Some(pa_stage 3 1[]).
Proof. vm_compute;discriminate. Qed.
Example empty_pair_block_excludes_restore : csteps pa_tm 5(pa_back StB[][])<>
 Some(pa_front StA[S2;S1][]).
Proof. vm_compute;discriminate. Qed.
Example frozen_A3_stays_A : pa_tm StA S3=Some(mkTrans S2 DR StA).
Proof. vm_compute;reflexivity. Qed.
Example altered_A3_is_distinct : pa_tm StA S3<>Some(mkTrans S2 DR StB).
Proof. vm_compute;discriminate. Qed.
Example frozen_B1_stays_B : pa_tm StB S1=Some(mkTrans S3 DL StB).
Proof. vm_compute;reflexivity. Qed.
Example altered_B1_is_distinct : pa_tm StB S1<>Some(mkTrans S3 DL StA).
Proof. vm_compute;discriminate. Qed.
