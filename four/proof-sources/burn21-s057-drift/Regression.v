From Coq Require Import List Arith Bool NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn21S057Drift Require Import RightBlankDrift.
Import ListNotations.
Example actual_escape_certificate : sd_escaped(csteps sd_tm(sd_count sd_stepsN)c0)=true.
Proof. exact sd_finite_certificate. Qed.
Example actual_preceding_A_certificate : sd_is_A(csteps sd_tm(sd_count sd_lastN)c0)=true.
Proof. exact sd_lastA_certificate. Qed.
Example actual_exact_attainment : AttainsSt sd_tm(sd_count sd_stepsN).
Proof. exact sd_attains. Qed.
Example one_blank_drift_step :
 csteps sd_tm 1(StB,([S3;S2],S0,[S0;S0]))=Some(StB,([S1;S3;S2],S0,[S0])).
Proof. reflexivity. Qed.
Example empty_right_tail_drifts :
 csteps sd_tm 4(StB,([S3],S0,[]))=Some(StB,([S1;S1;S1;S1;S3],S0,[])).
Proof. reflexivity. Qed.
Example nonempty_blank_padding_drifts :
 csteps sd_tm 4(StB,([S2;S1],S0,[S0;S0]))=Some(StB,([S1;S1;S1;S1;S2;S1],S0,[])).
Proof. reflexivity. Qed.
Example nonblank_right_tail_can_return_to_A :
 csteps sd_tm 2(StB,([],S0,[S1]))=Some(StA,([],S1,[S3])).
Proof. reflexivity. Qed.
Example nonblank_tail_rejected : sd_escaped(Some(StB,([],S0,[S0;S1])))=false.
Proof. reflexivity. Qed.
Example wrong_state_rejected : sd_escaped(Some(StA,([],S0,[])))=false.
Proof. reflexivity. Qed.
Example nonzero_head_rejected : sd_escaped(Some(StB,([],S1,[])))=false.
Proof. reflexivity. Qed.
Example halting_result_rejected : sd_escaped None=false.
Proof. reflexivity. Qed.
Example arbitrary_left_tape_does_not_prevent_drift : forall t l r,all_blank r=true->
 exists l' r',csteps sd_tm t(StB,(l,S0,r))=Some(StB,(l',S0,r'))/\all_blank r'=true.
Proof. exact sd_B_drift. Qed.
