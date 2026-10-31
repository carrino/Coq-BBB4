(** Exact entries, arbitrary contexts and excluded residue controls. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18CounterObligations Require Import CounterObligations.
From BBB24Burn24S056Counter Require Import Phase Fallback Return.
Import ListNotations.
Example reg_entry : csteps s56_tm 14 c0=Some(sf_G 1).
Proof. exact sf_entry. Qed.
Example reg_three_fallback : csteps s56_tm 9(StA,([S3;S3],S0,[]))=Some(sf_G 1).
Proof. reflexivity. Qed.
Example reg_mixed_fallback : csteps s56_tm 15(StA,(s56_in[false;true;false],S0,[]))=Some(sf_G 3).
Proof. reflexivity. Qed.
Example reg_X_context : csteps s56_tm 29(StA,(sf_X 1 2[S0;S2],S0,[S1;S0]))=
 Some(co_front StA(sf_Y 1 1[S0;S2])[S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_Y_context : csteps s56_tm 51(StA,(sf_Y 2 1[S3;S0],S0,[S2;S0]))=
 Some(co_front StA(sf_Z 2 0[S3;S0])[S2;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_Z_context : csteps s56_tm 39(StA,(sf_Z 1 1[S2;S0],S0,[S3;S0]))=
 Some(co_front StA(sf_X 2 0[S2;S0])[S3;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_terminal_three : csteps s56_tm 29
 (StA,(sf_P 1++S3::(sf_P 1++[S1;S3;S2;S0]),S0,[S1;S0]))=
 Some(co_front StA(sf_P 1++[S1;S3;S3]++sf_P 1++[S3;S2;S0])[S1;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_cap_one : csteps s56_tm 203(StA,(sf_X 3 1[S3],S0,[]))=Some(sf_G 23).
Proof. vm_compute;reflexivity. Qed.
Example reg_cap_two : csteps s56_tm 212(StA,(sf_X 2 2[S3],S0,[]))=Some(sf_G 19).
Proof. vm_compute;reflexivity. Qed.
Example reg_reset_one : csteps s56_tm 299(sf_G 7)=Some(sf_G 17).
Proof. vm_compute;reflexivity. Qed.
Example reg_reset_two : csteps s56_tm 585(sf_G 11)=Some(sf_G 25).
Proof. vm_compute;reflexivity. Qed.
Example reg_actual_61 : csteps s56_tm 61 c0=Some(sf_G 5).
Proof. vm_compute;reflexivity. Qed.
Example reg_divisible_zero : exists l,csteps s56_tm 26(sf_G 0)=Some(StB,(l,S0,[])).
Proof. eexists;vm_compute;reflexivity. Qed.
Example reg_divisible_three : exists l,csteps s56_tm 113(sf_G 3)=Some(StB,(l,S0,[])).
Proof. eexists;vm_compute;reflexivity. Qed.
Example reg_arbitrary_word_rejected : csteps s56_tm 10(StA,([S1;S3],S0,[]))=
 Some(StB,([S2;S2;S3],S2,[])).
Proof. exact s56_unsafe_seed. Qed.
Example reg_both_states : (forall N,exists t,N<=t /\VisitsAt s56_tm StA t)/\
 (forall N,exists t,N<=t /\VisitsAt s56_tm StB t).
Proof. split;[exact sf_A_recurrent|exact sf_B_recurrent]. Qed.
