(** Exact entry, arbitrary contexts, and rejected boundary relaxations. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn25S043Counter Require Import Core Return.
Import ListNotations.
Example reg_entry : csteps sg_tm 100852 c0=Some(sg_M 254).
Proof. exact sg_entry. Qed.
Example reg_consume_context : csteps sg_tm 16(sg_left 4[S1;S3;S0;S1])=
 Some(sg_left 7[S3;S0;S1]).
Proof. vm_compute;reflexivity. Qed.
Example reg_one_turn : csteps sg_tm 4(sg_front StB[S0;S3][S2;S2;S2;S1;S3;S0])=
 Some(sg_back StA[S3;S3;S3;S0;S3][S2;S3;S0]).
Proof. reflexivity. Qed.
Example reg_odd_twos : csteps sg_tm 5(sg_front StA[S1;S0][S2;S2;S2;S2;S2;S3;S0])=
 Some(sg_front StB[S3;S3;S3;S3;S3;S1;S0][S3;S0]).
Proof. reflexivity. Qed.
Example reg_A_three_context : csteps sg_tm 3(sg_back StA[S3;S3;S3;S0;S1][S2;S0])=
 Some(sg_back StA[S0;S1][S2;S2;S2;S2;S0]).
Proof. reflexivity. Qed.
Example reg_B_three_context : csteps sg_tm 3(sg_back StB[S3;S3;S3;S2;S1][S1;S3])=
 Some(sg_back StB[S2;S1][S0;S0;S0;S1;S3]).
Proof. reflexivity. Qed.
Example reg_defect_context : csteps sg_tm 12(sg_back StB[S2;S2;S2;S2;S1;S3][S0;S2;S0])=
 Some(sg_back StB[S1;S3][S0;S1;S1;S1;S1;S2;S0]).
Proof. reflexivity. Qed.
Example reg_finish_context : csteps sg_tm 17(sg_back StB[][S0;S1;S1;S1;S3;S0])=
 Some(sg_left 5[S3;S0]).
Proof. reflexivity. Qed.
Example reg_three_first : csteps sg_tm 13(StA,([S3;S3;S3;S3],S0,[]))=
 Some(StA,([S3;S3;S2;S2;S2;S2],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_three_final : csteps sg_tm 55(StA,(repeat S3 6,S0,[]))=Some(sg_C 5 3).
Proof. vm_compute;reflexivity. Qed.
Example reg_odd_reset : csteps sg_tm 96(sg_C 7 0)=Some(sg_C 5 8).
Proof. vm_compute;reflexivity. Qed.
Example reg_main_return : csteps sg_tm 390(sg_M 3)=Some(sg_M 12).
Proof. vm_compute;reflexivity. Qed.
Example reg_missing_tail : csteps sg_tm 10(sg_left 5[])=Some(StB,(repeat S3 7,S0,[])).
Proof. reflexivity. Qed.
Example reg_odd_one_run_changes_tail : csteps sg_tm 112(sg_C 5 1)=
 Some(sg_left 5(repeat S1 6++[S0;S0;S0;S1])).
Proof. vm_compute;reflexivity. Qed.
Example reg_even_reset_changes_tail : csteps sg_tm 58(sg_C 2 0)=
 Some(sg_left 5[S0;S0;S0;S1]).
Proof. vm_compute;reflexivity. Qed.
Example reg_both_states : (forall N,exists t,N<=t /\VisitsAt sg_tm StA t)/\
 (forall N,exists t,N<=t /\VisitsAt sg_tm StB t).
Proof. split;[exact sg_A_recurrent|exact sg_B_recurrent]. Qed.
