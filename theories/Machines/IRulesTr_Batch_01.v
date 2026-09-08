(** GENERATED from the MetaTr re-check sweep -- do not edit.

    The v1 IRules certificates that survive the strengthened
    per-instruction prefix gate: 97 of 250, each re-certified here as
    [NeverQuasiHaltsTr] by [irules_check_neverqhtr_sound] over the SAME
    certificate its state-level board uses (imported, not restated).
    These are the first rows of the transition-level Proven lookup
    tier (SCOPING_INSTR.md section 7.2). *)
From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta MetaTr.
From BBB4.Machines Require Import IRules_Batch_00 IRules_Batch_01 IRules_Batch_02 IRules_Batch_03 IRules_Batch_04 IRules_Batch_05 IRules_Batch_06 IRules_Batch_07 IRules_Batch_08.
Import ListNotations.
Open Scope Z_scope.

Theorem irtr_1RB1RA_0LC0LD_0RB1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0LC0LD_0RB1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0LC0LD_0RB1LC_1RA1LD cert_1RB1RA_0LC0LD_0RB1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1LC1LD_1RC0RA_0LC0LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1LC1LD_1RC0RA_0LC0LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1LC1LD_1RC0RA_0LC0LD cert_1RB1LA_1LC1LD_1RC0RA_0LC0LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LA_1LCXXX_0LD0LC_1RD0RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LA_1LCXXX_0LD0LC_1RD0RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LA_1LCXXX_0LD0LC_1RD0RA cert_1RB0LA_1LCXXX_0LD0LC_1RD0RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1LC1LC_0LD0LC_1RD0RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1LC1LC_0LD0LC_1RD0RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1LC1LC_0LD0LC_1RD0RA cert_1RB1LA_1LC1LC_0LD0LC_1RD0RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RBXXX_1LC0LA_0LD0LC_1RD0RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RBXXX_1LC0LA_0LD0LC_1RD0RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RBXXX_1LC0LA_0LD0LC_1RD0RB cert_1RBXXX_1LC0LA_0LD0LC_1RD0RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LC_1LC1LA_0LD0LC_1RD0RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LC_1LC1LA_0LD0LC_1RD0RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LC_1LC1LA_0LD0LC_1RD0RB cert_1RB0LC_1LC1LA_0LD0LC_1RD0RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_1LD0LA_0LA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_1LD0LA_0LA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_1LD0LA_0LA1LD cert_1RB1LA_1RC1RB_1LD0LA_0LA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_0LD0LA_1LB1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_0LD0LA_1LB1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_0LD0LA_1LB1LD cert_1RB1LA_1RC1RB_0LD0LA_1LB1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_0LD0LA_0RC1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_0LD0LA_0RC1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_0LD0LA_0RC1LD cert_1RB1LA_1RC1RB_0LD0LA_0RC1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LB_1RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LB_1RC1RB_1LD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LB_1RC1RB_1LD0RC_1LD1LA cert_1RB0LB_1RC1RB_1LD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_1RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_1RC1RB_1LD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_1RC1RB_1LD0RC_1LD1LA cert_1RB1RC_1RC1RB_1LD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_1LA1RB_1LD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_1LA1RB_1LD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_1LA1RB_1LD0RC_1LD1LA cert_1RB1RC_1LA1RB_1LD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0RD_1RC1RB_1LA1LC_1LC1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0RD_1RC1RB_1LA1LC_1LC1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0RD_1RC1RB_1LA1LC_1LC1RD cert_1RB0RD_1RC1RB_1LA1LC_1LC1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1RC1RB_1LC1LA_0RC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1RC1RB_1LC1LA_0RC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1RC1RB_1LC1LA_0RC0RD cert_1RB1RD_1RC1RB_1LC1LA_0RC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1RC1RB_1LC1LA_1LC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1RC1RB_1LC1LA_1LC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1RC1RB_1LC1LA_1LC0RD cert_1RB1RD_1RC1RB_1LC1LA_1LC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC1LB_0RA0RD_1LB1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC1LB_0RA0RD_1LB1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC1LB_0RA0RD_1LB1RD cert_1RB1RA_1LC1LB_0RA0RD_1LB1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC1RC_1LC1LA_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC1RC_1LC1LA_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC1RC_1LC1LA_1LB0RD cert_1RB1RD_0LC1RC_1LC1LA_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC1LB_1RA0RD_1LB1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC1LB_1RA0RD_1LB1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC1LB_1RA0RD_1LB1RD cert_1RB1RA_1LC1LB_1RA0RD_1LB1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0LD_0LD1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0LD_0LD1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0LD_0LD1LC_1RA1LD cert_1RB1RA_1LC0LD_0LD1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0LC0LD_0LD1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0LC0LD_0LD1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0LC0LD_0LD1LC_1RA1LD cert_1RB1RA_0LC0LD_0LD1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC1RB_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC1RB_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC1RB_1LC1LA_0RB0RD cert_1RB1RD_0LC1RB_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC1RB_1LC1LA_0RC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC1RB_1LC1LA_0RC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC1RB_1LC1LA_0RC0RD cert_1RB1RD_0LC1RB_1LC1LA_0RC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC1RB_1LC1LA_1LC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC1RB_1LC1LA_1LC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC1RB_1LC1LA_1LC0RD cert_1RB1RD_0LC1RB_1LC1LA_1LC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_0LA1RB_1LD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_0LA1RB_1LD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_0LA1RB_1LD0RC_1LD1LA cert_1RB1RC_0LA1RB_1LD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_0LD0LA_0LA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_0LD0LA_0LA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_0LD0LA_0LA1LD cert_1RB1LA_1RC1RB_0LD0LA_0LA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_1LD0LA_1LB1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_1LD0LA_1LB1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_1LD0LA_1LB1LD cert_1RB1LA_1RC1RB_1LD0LA_1LB1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LA_1LB0LC_0LD0LC_1RD0RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LA_1LB0LC_0LD0LC_1RD0RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LA_1LB0LC_0LD0LC_1RD0RA cert_1RB0LA_1LB0LC_0LD0LC_1RD0RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1LA0LC_1RD1LC_1RB1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1LA0LC_1RD1LC_1RB1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1LA0LC_1RD1LC_1RB1RD cert_1RB1LA_1LA0LC_1RD1LC_1RB1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0LD_1RB1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0LD_1RB1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0LD_1RB1LC_1RA1LD cert_1RB1RA_1LC0LD_1RB1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0LC0LD_1LA1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0LC0LD_1LA1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0LC0LD_1LA1LC_1RA1LD cert_1RB1RA_0LC0LD_1LA1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_1LD0LA_1RC1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_1LD0LA_1RC1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_1LD0LA_1RC1LD cert_1RB1LA_1RC1RB_1LD0LA_1RC1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1LA1LC_0LD0LC_1RD1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1LA1LC_0LD0LC_1RD1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1LA1LC_0LD0LC_1RD1RB cert_1RB1LA_1LA1LC_0LD0LC_1RD1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1LA1LC_1RD0LC_1RD1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1LA1LC_1RD0LC_1RD1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1LA1LC_1RD0LC_1RD1RB cert_1RB1LA_1LA1LC_1RD0LC_1RD1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LB0LC_1LA1RC_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LB0LC_1LA1RC_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LB0LC_1LA1RC_0RB0RD cert_1RB1RD_1LB0LC_1LA1RC_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0RB_1LC1LD_0RA0LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0RB_1LC1LD_0RA0LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0RB_1LC1LD_0RA0LA cert_1RB1RA_1LC0RB_1LC1LD_0RA0LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0RB_1LC1LD_0RA1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0RB_1LC1LD_0RA1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0RB_1LC1LD_0RA1RB cert_1RB1RA_1LC0RB_1LC1LD_0RA1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC0RC_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC0RC_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC0RC_1LC1LA_0RB0RD cert_1RB1RD_0LC0RC_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LB_0LC0LB_0LD1LC_1RD1RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LB_0LC0LB_0LD1LC_1RD1RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LB_0LC0LB_0LD1LC_1RD1RA cert_1RB1LB_0LC0LB_0LD1LC_1RD1RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LB1LC_0RA1RD_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LB1LC_0RA1RD_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LB1LC_0RA1RD_0RB0RD cert_1RB1RA_1LB1LC_0RA1RD_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LB1LC_0RA1RD_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LB1LC_0RA1RD_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LB1LC_0RA1RD_1LB0RD cert_1RB1RA_1LB1LC_0RA1RD_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0LD_0RB1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0LD_0RB1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0LD_0RB1LC_1RA1LD cert_1RB1RA_1LC0LD_0RB1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_0RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_0RC1RB_0RD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_0RC1RB_0RD0RC_1LD1LA cert_1RB1RC_0RC1RB_0RD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_0RA1LB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_0RA1LB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_0RA1LB cert_1RB1RD_0RC0RB_1LC0LA_0RA1LB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_1LA0RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_1LA0RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_1LA0RB cert_1RB1RD_0RC0RB_1LC0LA_1LA0RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_0RBXXX_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_0RBXXX.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_0RBXXX cert_1RB1RD_0RC0RB_1LC0LA_0RBXXX 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RD_1LC0LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RD_1LC0LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RD_1LC0LA_0RB0RD cert_1RB1RD_0RC0RD_1LC0LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_0LA1LC_0LD0LC_1RD1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_0LA1LC_0LD0LC_1RD1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_0LA1LC_0LD0LC_1RD1RB cert_1RB1LA_0LA1LC_0LD0LC_1RD1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_0RD0RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_0RD0RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_0RD0RB cert_1RB1RD_0RC0RB_1LC0LA_0RD0RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_0LA1LC_1RD0LC_1RD1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_0LA1LC_1RD0LC_1RD1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_0LA1LC_1RD0LC_1RD1RB cert_1RB1LA_0LA1LC_1RD0LC_1RD1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_1LD1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_1LD1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_1LD1RB cert_1RB1RD_0RC0RB_1LC0LA_1LD1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RB_1LC0LA_1RD1LB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RB_1LC0LA_1RD1LB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RB_1LC0LA_1RD1LB cert_1RB1RD_0RC0RB_1LC0LA_1RD1LB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0RB_1LC1LD_1RA0LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0RB_1LC1LD_1RA0LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0RB_1LC1LD_1RA0LA cert_1RB1RA_1LC0RB_1LC1LD_1RA0LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0RB_1LC1LD_1RA1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0RB_1LC1LD_1RA1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0RB_1LC1LD_1RA1RB cert_1RB1RA_1LC0RB_1LC1LD_1RA1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LB_0LC0LB_0RD1LC_1RD1RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LB_0LC0LB_0RD1LC_1RD1RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LB_0LC0LB_0RD1LC_1RD1RA cert_1RB1LB_0LC0LB_0RD1LC_1RD1RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC1RB_1LC1LA_0LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC1RB_1LC1LA_0LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC1RB_1LC1LA_0LB0RD cert_1RB1RD_0RC1RB_1LC1LA_0LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC1RB_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC1RB_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC1RB_1LC1LA_0RB0RD cert_1RB1RD_0RC1RB_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC1RB_1LC1LA_0RC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC1RB_1LC1LA_0RC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC1RB_1LC1LA_0RC0RD cert_1RB1RD_0RC1RB_1LC1LA_0RC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_1LA1RB_0RD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_1LA1RB_0RD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_1LA1RB_0RD0RC_1LD1LA cert_1RB1RC_1LA1RB_0RD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC1RB_1LC1LA_1LC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC1RB_1LC1LA_1LC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC1RB_1LC1LA_1LC0RD cert_1RB1RD_0RC1RB_1LC1LA_1LC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_1LD0LA_0RC1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_1LD0LA_0RC1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_1LD0LA_0RC1LD cert_1RB1LA_1RC1RB_1LD0LA_0RC1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_0LC0LB_1RC1RD_1LA1LB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_0LC0LB_1RC1RD_1LA1LB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_0LC0LB_1RC1RD_1LA1LB cert_1RB1LA_0LC0LB_1RC1RD_1LA1LB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC0RC_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC0RC_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC0RC_1LC1LA_0RB0RD cert_1RB1RD_1LC0RC_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC0RC_1LC1LA_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC0RC_1LC1LA_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC0RC_1LC1LA_1LB0RD cert_1RB1RD_1LC0RC_1LC1LA_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RBXXX_0RC0RB_1LC0LD_1LA0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RBXXX_0RC0RB_1LC0LD_1LA0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RBXXX_0RC0RB_1LC0LD_1LA0RD cert_1RBXXX_0RC0RB_1LC0LD_1LA0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RB_0RC0RB_1LC0LD_1LA1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RB_0RC0RB_1LC0LD_1LA1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RB_0RC0RB_1LC0LD_1LA1RD cert_1RB1RB_0RC0RB_1LC0LD_1LA1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_0LA0LC_1RD1LC_1RB1RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_0LA0LC_1RD1LC_1RB1RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_0LA0LC_1RD1LC_1RB1RD cert_1RB1LA_0LA0LC_1RD1LC_1RB1RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_0RC1RB_1LD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_0RC1RB_1LD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_0RC1RB_1LD0RC_1LD1LA cert_1RB1RC_0RC1RB_1LD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LC0LD_1LA1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LC0LD_1LA1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LC0LD_1LA1LC_1RA1LD cert_1RB1RA_1LC0LD_1LA1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC0RB_1LC1LD_0RD0LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC0RB_1LC1LD_0RD0LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC0RB_1LC1LD_0RD0LA cert_1RB1RA_0RC0RB_1LC1LD_0RD0LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0RD_0RC0RB_1LC0LA_1LAXXX_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0RD_0RC0RB_1LC0LA_1LAXXX.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0RD_0RC0RB_1LC0LA_1LAXXX cert_1RB0RD_0RC0RB_1LC0LA_1LAXXX 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LB1LC_1RA1RD_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LB1LC_1RA1RD_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LB1LC_1RA1RD_0RB0RD cert_1RB1RA_1LB1LC_1RA1RD_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_1LB1LC_1RA1RD_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_1LB1LC_1RA1RD_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_1LB1LC_1RA1RD_1LB0RD cert_1RB1RA_1LB1LC_1RA1RD_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LA_0RC0RB_1LC1LD_0RA1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LA_0RC0RB_1LC1LD_0RA1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LA_0RC0RB_1LC1LD_0RA1RB cert_1RB0LA_0RC0RB_1LC1LD_0RA1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC0RB_1LC1LD_0RA1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC0RB_1LC1LD_0RA1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC0RB_1LC1LD_0RA1RB cert_1RB1RA_0RC0RB_1LC1LD_0RA1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC1LD_1LC0LA_0LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC1LD_1LC0LA_0LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC1LD_1LC0LA_0LB0RD cert_1RB1RA_0RC1LD_1LC0LA_0LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0LB_1RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0LB_1RC1RB_0RD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0LB_1RC1RB_0RD0RC_1LD1LA cert_1RB0LB_1RC1RB_0RD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC1LD_1LC0LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC1LD_1LC0LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC1LD_1LC0LA_0RB0RD cert_1RB1RA_0RC1LD_1LC0LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC1LD_1LC0LA_0RC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC1LD_1LC0LA_0RC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC1LD_1LC0LA_0RC0RD cert_1RB1RA_0RC1LD_1LC0LA_0RC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_1RC1RB_0RD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_1RC1RB_0RD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_1RC1RB_0RD0RC_1LD1LA cert_1RB1RC_1RC1RB_0RD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC1LD_1LC0LA_1LC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC1LD_1LC0LA_1LC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC1LD_1LC0LA_1LC0RD cert_1RB1RA_0RC1LD_1LC0LA_1LC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_1RC0RD_0LB0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_1RC0RD_0LB0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_1RC0RD_0LB0RC_1LD1LA cert_1RB1RC_1RC0RD_0LB0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0RC_0LA1RB_1LD1RC_1LA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0RC_0LA1RB_1LD1RC_1LA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0RC_0LA1RB_1LD1RC_1LA1LD cert_1RB0RC_0LA1RB_1LD1RC_1LA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LA_1RC1RB_0LD0LA_1RC1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LA_1RC1RB_0LD0LA_1RC1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LA_1RC1RB_0LD0LA_1RC1LD cert_1RB1LA_1RC1RB_0LD0LA_1RC1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1LB_0LC0LB_1RD1LC_1RD1RA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1LB_0LC0LB_1RD1LC_1RD1RA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1LB_0LC0LB_1RD1LC_1RD1RA cert_1RB1LB_0LC0LB_1RD1LC_1RD1RA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC1RB_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC1RB_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC1RB_1LC1LA_0RB0RD cert_1RB1RD_1LC1RB_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC0RB_1LC1LD_1RA0LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC0RB_1LC1LD_1RA0LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC0RB_1LC1LD_1RA0LA cert_1RB1RA_0RC0RB_1LC1LD_1RA0LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC1RB_1LC1LA_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC1RB_1LC1LA_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC1RB_1LC1LA_1LB0RD cert_1RB1RD_1LC1RB_1LC1LA_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC1RB_1LC1LA_0RC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC1RB_1LC1LA_0RC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC1RB_1LC1LA_0RC0RD cert_1RB1RD_1LC1RB_1LC1LA_0RC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0RC0RB_1LC1LD_1RA1RB_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0RC0RB_1LC1LD_1RA1RB.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0RC0RB_1LC1LD_1RA1RB cert_1RB1RA_0RC0RB_1LC1LD_1RA1RB 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_1LC1RB_1LC1LA_1LC0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_1LC1RB_1LC1LA_1LC0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_1LC1RB_1LC1LA_1LC0RD cert_1RB1RD_1LC1RB_1LC1LA_1LC0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RC_0LA1RB_0RD0RC_1LD1LA_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RC_0LA1RB_0RD0RC_1LD1LA.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RC_0LA1RB_0RD0RC_1LD1LA cert_1RB1RC_0LA1RB_0RD0RC_1LD1LA 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RA_0LC0LD_1RB1LC_1RA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RA_0LC0LD_1RB1LC_1RA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RA_0LC0LD_1RB1LC_1RA1LD cert_1RB1RA_0LC0LD_1RB1LC_1RA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0RC_1LA1RB_1LD1RC_1LA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0RC_1LA1RB_1LD1RC_1LA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0RC_1LA1RB_1LD1RC_1LA1LD cert_1RB0RC_1LA1RB_1LD1RC_1LA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RC_1LC1LA_0LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RC_1LC1LA_0LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RC_1LC1LA_0LB0RD cert_1RB1RD_0RC0RC_1LC1LA_0LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0RC0RC_1LC1LA_0RB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0RC0RC_1LC1LA_0RB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0RC0RC_1LC1LA_0RB0RD cert_1RB1RD_0RC0RC_1LC1LA_0RB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB0RC_0RC1RB_1LD1RC_1LA1LD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB0RC_0RC1RB_1LD1RC_1LA1LD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB0RC_0RC1RB_1LD1RC_1LA1LD cert_1RB0RC_0RC1RB_1LD1RC_1LA1LD 300000%nat).
  vm_compute. reflexivity.
Qed.

Theorem irtr_1RB1RD_0LC1RD_1LC1LA_1LB0RD_never_quasihalts_tr :
  NeverQuasiHaltsTr tm_1RB1RD_0LC1RD_1LC1LA_1LB0RD.
Proof.
  apply (irules_check_neverqhtr_sound tm_1RB1RD_0LC1RD_1LC1LA_1LB0RD cert_1RB1RD_0LC1RD_1LC1LA_1LB0RD 300000%nat).
  vm_compute. reflexivity.
Qed.
