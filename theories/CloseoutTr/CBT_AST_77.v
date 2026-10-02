(** Transition-level closeout: pair transfers over a left block stack. *)
From Coq Require Import List Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Counters Require Import PairStackTr.
Import ListNotations.

(* spec 1RB1LA_1LB0RC_1LD1RC_0LD0LA *)
Definition r_AST_77_0000 : list (option Trans) :=
 [t1RB;t1LA;t1LB;t0RC;t1LD;t1RC;t0LD;t0LA].
Local Definition tm := mirror_tm (row_to_tm r_AST_77_0000).

Lemma cv_AST_77_0000 : coversTr (row_to_tm r_AST_77_0000).
Proof.
 apply coversTr_nqh,neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 apply (pair_stack_neverqhtr tm eq_refl eq_refl eq_refl eq_refl
   eq_refl eq_refl eq_refl eq_refl).
 exists 17,[2],1. split;[cbn [pc_wf];lia|]. split;[lia|].
 assert (E : exists c, csteps tm 17 c0=Some c /\ ceqb c (pc_D [2] 1)=true).
 { eexists. split;vm_compute;reflexivity. }
 destruct E as (c&Ec&El). rewrite <-lift_c0.
 pose proof (csteps_lift tm 17 c0 c Ec) as E.
 rewrite (ceqb_lift _ _ El) in E. exact E.
Qed.

Definition cbtrows_AST_77 : list (list (option Trans)) := [r_AST_77_0000].
Lemma cbt_AST_77_covers : Forall coversTr (map row_to_tm cbtrows_AST_77).
Proof. constructor;[exact cv_AST_77_0000|constructor]. Qed.
