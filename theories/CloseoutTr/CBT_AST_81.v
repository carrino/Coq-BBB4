(** Transition closeout: a binary counter whose boundary resets at overflow. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import BinaryResetTr LapGlueTr.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
Import ListNotations.

(* spec 1RB0RC_1LC0LD_1RA1RD_1RC1LB *)
Definition r_AST_81_0000 : list (option Trans) :=
 [t1RB;t0RC;t1LC;t0LD;t1RA;t1RD;t1RC;t1LB].
Local Definition tm := row_to_tm r_AST_81_0000.
Local Lemma sw : srun tm false true br_sweep_ch br_sweep_s = Some (br_sweep_e,4,14).
Proof. vm_compute;reflexivity. Qed.
Local Lemma reset : srun tm true false br_reset_ch br_reset_s = Some (br_reset_e,4,9).
Proof. vm_compute;reflexivity. Qed.
Local Lemma finish : srun tm true true br_finish_ch br_finish_s = Some (br_finish_e,2,10).
Proof. vm_compute;reflexivity. Qed.
Local Lemma fires : forall t, exists ch, srun_instr tm false true ch br_sweep_s = Some t.
Proof.
 intros [[] []].
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 3)]. vm_compute;reflexivity.
 - exists []. reflexivity.
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 4)]. vm_compute;reflexivity.
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 7)]. vm_compute;reflexivity.
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 2)]. vm_compute;reflexivity.
 - exists [(SRotR 1); (SWin 1)]. vm_compute;reflexivity.
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 1)]. vm_compute;reflexivity.
 - exists [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 6)]. vm_compute;reflexivity.
Qed.

Lemma cv_AST_81_0000 : coversTr (row_to_tm r_AST_81_0000).
Proof.
 apply coversTr_nqh. change (NeverQuasiHaltsTr tm).
 apply binary_reset_neverqhtr;
   first [exact sw|exact reset|exact finish|exact fires|reflexivity|idtac].
 exists 17,1,[S1],false.
 assert (E : exists c, csteps tm 17 c0=Some c /\ ceqb c (br_anchor (1,([S1],false)))=true).
 { eexists. split;vm_compute;reflexivity. }
 destruct E as (c&Ec&El). rewrite <-lift_c0.
 rewrite (csteps_lift _ _ _ _ Ec),(ceqb_lift _ _ El). reflexivity.
Qed.
Definition cbtrows_AST_81 : list (list (option Trans)) := [r_AST_81_0000].
Lemma cbt_AST_81_covers : Forall coversTr (map row_to_tm cbtrows_AST_81).
Proof. constructor;[exact cv_AST_81_0000|constructor]. Qed.
