(** RepWL at the reflected seed alignment. *)
From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.CensusTr Require Import RepWLTr TNF_QHTr.
Import ListNotations.
(* spec 1RB0RD_1LC0LC_1LD1LC_1RA0RB *)
Definition r_AST_94_0000:list(option Trans):=[t1RB;t0RD;t1LC;t0LC;t1LD;t1LC;t1RA;t0RB].
Lemma cv_AST_94_0000:coversTr(row_to_tm r_AST_94_0000).
Proof. apply coversTr_nqh, neverqhtr_mirror,
 (rw_tier_tr_sound _ 6 2 0 (230*1000) 25).
 vm_cast_no_check(eq_refl true). Qed.
(* spec 1RB1RA_1LC0LD_1LD0LB_1RA0RA *)
Definition r_AST_94_0001:list(option Trans):=[t1RB;t1RA;t1LC;t0LD;t1LD;t0LB;t1RA;t0RA].
Lemma cv_AST_94_0001:coversTr(row_to_tm r_AST_94_0001).
Proof. apply coversTr_nqh, neverqhtr_mirror,
 (rw_tier_tr_sound _ 6 2 0 (210*1000) 24).
 vm_cast_no_check(eq_refl true). Qed.
Definition cbtrows_AST_94:list(list(option Trans)) := [r_AST_94_0000;r_AST_94_0001].
Lemma cbt_AST_94_covers:Forall coversTr(map row_to_tm cbtrows_AST_94).
Proof. exact(Forall_cons _ cv_AST_94_0000(Forall_cons _ cv_AST_94_0001(Forall_nil _))). Qed.
