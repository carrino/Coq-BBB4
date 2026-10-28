(** Discharge every explicit odd-helper premise of the outer six-cycle. *)
From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn26S052Counter Require Import Core Odd Outer.
Import ListNotations.
Lemma sp_H2 : forall k r,sh_reach(sh_H(3*k+2)r)(sh_AF 5(6*k+3)r).
Proof. intros;exists(so_A_cost k);apply so_normalize_A. Qed.
Lemma sp_H3 : forall k r,sh_reach(sh_H(3*k+3)r)(sh_AF 7(6*k+3)r).
Proof. intros;exists(so_B_cost k);apply so_normalize_B. Qed.
Lemma sp_HP : forall k r,sh_reach(sh_H(3*k+1)r)
 (sh_AF 1 0(S3::(repeat S2(6*k+4)++r))).
Proof. intros;exists(so_bad_cost k);apply so_bad_prefix. Qed.
Lemma sp_HT : forall k r,sh_reach(sh_AF 5 3(repeat S3(6*k)++r))(sh_AF 5(6*k+3)r).
Proof. intros;exists(so_train_cost k);apply so_train_normalize. Qed.
Theorem sh_main_next : forall k,exists t,0<t /\
 csteps sh_tm t(sh_main 2(6*k+4))=Some(sh_main 2(6*(S k)+4)).
Proof. exact(sh_main_next_conditional sp_H2 sp_H3 sp_HP sp_HT). Qed.
Theorem sh_A_recurrent : forall N,exists t,N<=t /\VisitsAt sh_tm StA t.
Proof. exact(sh_A_recurrent_conditional sp_H2 sp_H3 sp_HP sp_HT). Qed.
Theorem sh_B_recurrent : forall N,exists t,N<=t /\VisitsAt sh_tm StB t.
Proof. exact(sh_B_recurrent_conditional sp_H2 sp_H3 sp_HP sp_HT). Qed.
Theorem sh_sound : NonHalt sh_tm /\QHBound 0 sh_tm.
Proof. exact(sh_sound_conditional sp_H2 sp_H3 sp_HP sp_HT). Qed.
Print Assumptions sh_main_next.
Print Assumptions sh_sound.
