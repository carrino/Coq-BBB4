(** Transition-level closeout: cube rounds over a growing block stack. *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Counters Require Import StackCubeTr.
Import ListNotations.

(* spec 1RB1LA_0RC0RD_1LC0LA_1RB0RC *)
Definition r_AST_75_0000 : list (option Trans) :=
 [t1RB;t1LA;t0RC;t0RD;t1LC;t0LA;t1RB;t0RC].
Local Definition tm := mirror_tm (row_to_tm r_AST_75_0000).

Lemma cv_AST_75_0000 : coversTr (row_to_tm r_AST_75_0000).
Proof.
 apply coversTr_nqh,neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 eapply (stack_cube_neverqhtr tm eq_refl eq_refl eq_refl eq_refl
   eq_refl eq_refl eq_refl 1).
 - intros L R. reflexivity.
 - exists 19,1,0,0,[].
   assert (E : exists c, csteps tm 19 c0 = Some c /\ ceqb c (sc_C 1 0 0 []) = true).
   { eexists. split; vm_compute; reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   pose proof (csteps_lift tm 19 c0 c Ec) as E.
   rewrite (ceqb_lift _ _ El) in E. exact E.
Qed.

Definition cbtrows_AST_75 : list (list (option Trans)) := [r_AST_75_0000].
Lemma cbt_AST_75_covers : Forall coversTr (map row_to_tm cbtrows_AST_75).
Proof. constructor; [exact cv_AST_75_0000|constructor]. Qed.
