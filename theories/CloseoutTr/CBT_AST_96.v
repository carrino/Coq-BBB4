(** Long translated cycle: bootstrap 24,378,294; period 2,575,984;
    displacement +1440; no left window is needed. *)
From Coq Require Import Arith List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers Require Import TCyclerAllNTr.
Import ListNotations.

(* spec 1RB0LA_0RC1LA_1RD0RD_1LB1RB *)
Definition r_AST_96_0000 : list (option Trans) :=
  [t1RB; t0LA; t0RC; t1LA; t1RD; t0RD; t1LB; t1RB].
Lemma cv_AST_96_0000 : coversTr (row_to_tm r_AST_96_0000).
Proof.
  apply coversTr_nqh, (tcycler_all_N_check_sound _ 24378294%N 2575984 0).
  vm_cast_no_check (eq_refl true).
Qed.

Definition cbtrows_AST_96 : list (list (option Trans)) := [r_AST_96_0000].
Lemma cbt_AST_96_covers : Forall coversTr (map row_to_tm cbtrows_AST_96).
Proof. exact (Forall_cons _ cv_AST_96_0000 (Forall_nil _)). Qed.
