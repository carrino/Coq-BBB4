From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn32S042 Require Import Programs Symbolic Counter Final.
Import ListNotations.
Example s42_reg_entry : csteps s42_tm 12565 c0=Some(s42_family 42).
Proof. exact s42_boot. Qed.
Example s42_reg_return_small : exists k,0<k/\csteps s42_tm k(s42_family 0)=Some(s42_family 27).
Proof. exact(s42_return 0). Qed.
Example s42_reg_F : forall n m,exists k,38<=k /\csteps s42_tm k(s42_Fconf(S n)m)=Some(s42_Fconf n(S m)).
Proof. exact s42_F_step. Qed.
Example s42_reg_G : forall n m,exists k,36<=k /\csteps s42_tm k(s42_Gconf(S n)m)=Some(s42_Gconf n(S m)).
Proof. exact s42_G_step. Qed.
Example s42_reg_unknown_zero : s42_pop[(S3,s42_E 0 1 0)]=None.
Proof. reflexivity. Qed.
Example s42_reg_unknown_parity : s42_two(s42_C StA S2[][(S2,s42_E 0 1 0)])=None.
Proof. reflexivity. Qed.
Lemma s42_B_drift : forall n l,csteps s42_tm n(StB,(l,S0,[]))=
 Some(StB,(repeat S0 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s42_tm n(StB,(S0::l,S0,[]))=Some(StB,(S0::(repeat S0 n++l),S0,[]))).
 rewrite IHn,s42_shift;reflexivity.
Qed.
Example s42_reg_unsafe_seed : forall n,csteps s42_tm(43+n)
 (StA,([S2;S0;S3;S3;S3;S0],S0,[]))=
 Some(StB,(repeat S0 n++[S3;S3;S3;S3;S3;S2;S0;S3;S0],S0,[])).
Proof.
 intro n;rewrite csteps_add.
 change(csteps s42_tm n(StB,([S3;S3;S3;S3;S3;S2;S0;S3;S0],S0,[]))=
 Some(StB,(repeat S0 n++[S3;S3;S3;S3;S3;S2;S0;S3;S0],S0,[]))).
 apply s42_B_drift.
Qed.
Example s42_reg_A_recurs : forall N,exists k,N<=k/\VisitsAt s42_tm StA k.
Proof. exact s42_A_late. Qed.
Example s42_reg_B_recurs : forall N,exists k,N<=k/\VisitsAt s42_tm StB k.
Proof. exact s42_B_late. Qed.
Example s42_reg_state_zero : QHBound 0 s42_tm.
Proof. exact s42_state_zero. Qed.
Print Assumptions s42_reg_unsafe_seed.
