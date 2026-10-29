(** All four recursive families, each outer phase, and excluded seeds. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn26S052Counter Require Import Core Odd Outer Proof.
Import ListNotations.
Example reg_entry : csteps sh_tm 142 c0=Some(sh_main 2 4).
Proof. exact sh_entry. Qed.
Example reg_first_cycle : csteps sh_tm 1114(sh_main 2 4)=Some(sh_main 2 10).
Proof. vm_compute;reflexivity. Qed.
Example reg_second_cycle : csteps sh_tm 4206(sh_main 2 10)=Some(sh_main 2 16).
Proof. vm_compute;reflexivity. Qed.
Example reg_bad_prefix_context : csteps sh_tm 182(sh_H 4[S3;S0])=
 Some(sh_AF 1 0(S3::(repeat S2 10++[S3;S0]))).
Proof. vm_compute;reflexivity. Qed.
Example reg_good_A_context : csteps sh_tm 205(sh_H 5[S0;S2])=Some(sh_AF 5 9[S0;S2]).
Proof. vm_compute;reflexivity. Qed.
Example reg_good_B_context : csteps sh_tm 473(sh_H 6[S1;S0])=Some(sh_AF 7 9[S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_accumulated_train : csteps sh_tm 374(sh_AF 5 3(repeat S3 6++[S3;S0]))=
 Some(sh_AF 5 9[S3;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_five_even_context : csteps sh_tm 45(sh_AF 5 4[S3;S1;S0])=
 Some(sh_AF 5 5[S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_five_odd_context : csteps sh_tm 37(sh_AF 5 5[S3;S2;S0])=
 Some(sh_H 2[S3;S2;S2;S2;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_two_threes : csteps sh_tm 42(sh_AF 1 6[S3;S3;S0;S2])=
 Some(sh_AF 7 2[S0;S2]).
Proof. vm_compute;reflexivity. Qed.
Example reg_three_twothrees : csteps sh_tm 50(sh_AF 3 6[S3;S3;S1;S0])=
 Some(sh_AF 1 10[S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_two_phase : csteps sh_tm 41(sh_main 2 4)=Some(sh_main 3 4).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_three_phase : csteps sh_tm 45(sh_main 3 4)=Some(sh_main 4 4).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_four_two_phase : csteps sh_tm 111(sh_main 4 4)=Some(sh_main 6 3).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_six_phase : csteps sh_tm 239(sh_main 6 3)=Some(sh_main 4 6).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_four_zero_phase : csteps sh_tm 195(sh_main 4 6)=Some(sh_main 8 3).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_eight_phase : csteps sh_tm 483(sh_main 8 3)=Some(sh_main 2 10).
Proof. vm_compute;reflexivity. Qed.
Example reg_reject_seed_one_five : csteps sh_tm 57(sh_main 1 5)=
 Some(StB,(repeat S3 7++[S0],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_reject_seed_four_two : csteps sh_tm 79(sh_main 4 2)=
 Some(StB,(repeat S3 7++[S0],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_both_states : (forall N,exists t,N<=t /\VisitsAt sh_tm StA t)/\
 (forall N,exists t,N<=t /\VisitsAt sh_tm StB t).
Proof. split;[exact sh_A_recurrent|exact sh_B_recurrent]. Qed.
