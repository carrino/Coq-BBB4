(** Positive arbitrary-context identities and rejected boundary relaxations. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn23S062Counter Require Import S062Core Return.
Import ListNotations.
Example reg_entry : csteps s62_tm 5 c0=Some(s62_main 0 [] []).
Proof. exact s62_entry. Qed.
Example reg_pair_context : csteps s62_tm 2(s62_back StB[S1;S1;S0;S2][S3;S0])=
 Some(s62_back StB[S0;S2][S2;S3;S3;S0]).
Proof. reflexivity. Qed.
Example reg_launch_context : csteps s62_tm 3(s62_back StB[S1;S3;S2;S0][S1;S0])=
 Some(s62_front StA[S1;S1;S2;S0][S1;S0]).
Proof. reflexivity. Qed.
Example reg_double_launch : csteps s62_tm 19
 (s62_back StB[S1;S3;S1;S3;S0;S3](s62_guard[S2;S3;S3]2))=
 Some(s62_main 3(s62_decode[S2;S3;S3]++[S1;S1;S1;S3])[S0;S3]).
Proof. vm_compute;reflexivity. Qed.
Example reg_plain_launch : csteps s62_tm 5(s62_back StA[S3;S0;S3][S3;S3;S3;S3])=
 Some(s62_main 0[S1;S1;S1][S0;S3]).
Proof. reflexivity. Qed.
Example reg_guard_launch : csteps s62_tm 14
 (s62_back StA[S3;S3;S0](S3::s62_guard[S3;S2]1))=
 Some(s62_main 2(s62_decode[S3;S2]++[S1;S1])[S3;S0]).
Proof. vm_compute;reflexivity. Qed.
Example reg_left_march_context : forall r,csteps s62_tm 5(s62_dead[S3]r)=
 Some(s62_dead[S3](S3::r)).
Proof. intros;reflexivity. Qed.
Example reg_dead_rotor_crossing : exists n l,Forall s62_03 l /\
 csteps s62_tm n(s62_front StB[S3;S0;S3][S3;S1;S2])=
 Some(s62_front StB l[S1;S2]).
Proof. apply s62_B_three_cross;constructor;[right;reflexivity|constructor;[left;reflexivity|constructor;[right;reflexivity|constructor]]]. Qed.
Example reg_unmatched_one : csteps s62_tm 1(s62_back StB[S1;S0;S3](s62_guard[]2))=
 Some(s62_dead[S3](S3::s62_guard[]2)).
Proof. reflexivity. Qed.
Example reg_actual_28 : csteps s62_tm 28 c0=Some(s62_main 0[S1;S1][S3]).
Proof. vm_compute;reflexivity. Qed.
Example reg_actual_132 : csteps s62_tm 132 c0=
 Some(s62_main 0[S1][S0;S3;S0;S3;S0;S3;S0;S3]).
Proof. vm_compute;reflexivity. Qed.
Example reg_reject_unguarded_right_one : csteps s62_tm 17(s62_dead[][S1])=
 Some(StB,([S3;S3;S3;S0;S0;S3;S3],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_reject_single_leading_one : csteps s62_tm 13(StA,([S1;S3],S0,[]))=
 Some(StB,([S0;S0;S3;S3],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_reject_one_left_of_zero : csteps s62_tm 33(StA,([S1;S1;S0;S1;S3],S0,[]))=
 Some(StB,([S0;S3;S0;S0;S0;S3;S3],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Example reg_both_states : (forall N,exists t,N<=t /\VisitsAt s62_tm StA t)/\
 (forall N,exists t,N<=t /\VisitsAt s62_tm StB t).
Proof. split;[exact s62_A_recurrent|exact s62_B_recurrent]. Qed.
