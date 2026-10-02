(** Transition closeout: a binary counter with two separated carry passes. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import BinaryGateTokenTr ValueLapTr LapGlueTr.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
Import ListNotations.

(* spec 0RB1LC_1LC1RD_1LA0LC_0RD1RB *)
Definition r_AST_79_0000 : list (option Trans) :=
 [t0RB;t1LC;t1LC;t1RD;t1LA;t0LC;t0RD;t1RB].
Local Definition tm := row_to_tm r_AST_79_0000.
Local Lemma sw1 : srun tm false true bg_ch1 bg_s1 = Some (bg_e1,6,4).
Proof. vm_compute;reflexivity. Qed.
Local Lemma sw2 : srun tm false true bg_ch2 bg_s2 = Some (bg_e2,6,2).
Proof. vm_compute;reflexivity. Qed.
Local Lemma sw3 : srun tm false true bg_ch3 bg_s3 = Some (bg_e3,6,8).
Proof. vm_compute;reflexivity. Qed.
Local Lemma fw : forall t, t<>(StA,S1) -> exists ch,
 srun_instr tm false true ch bg_f3 = Some t.
Proof.
 intros [[] []] H.
 - exists [(SWin 1); (SCycR 3); (SWinR 2); (SCycL 3 0); (SWin 2)]. vm_compute;reflexivity.
 - contradiction H;reflexivity.
 - exists [(SWin 1); (SCycR 3); (SWinR 1)]. vm_compute;reflexivity.
 - exists [(SWin 1); (SCycR 3); (SWinR 2); (SCycL 3 0); (SWin 3)]. vm_compute;reflexivity.
 - exists [(SWin 1); (SCycR 3); (SWinR 2); (SCycL 3 0); (SWin 1)]. vm_compute;reflexivity.
 - exists [(SWin 1); (SCycR 3); (SWinR 2)]. vm_compute;reflexivity.
 - exists []. reflexivity.
 - exists [(SWin 1)]. reflexivity.
Qed.

Lemma cv_AST_79_0000 : coversTr (row_to_tm r_AST_79_0000).
Proof.
 apply coversTr_nqh. change (NeverQuasiHaltsTr tm).
 apply (value_lap_neverqhtr tm (list Sym) bg_next bg_anchor []).
 - exists 21.
   assert (E : exists c, csteps tm 21 c0 = Some c /\ ceqb c (bg_anchor 0 []) = true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.
 - intros n w. exists (bg_cost n w),(bg_anchor (S n) (bg_next w)).
   split;[|split;[reflexivity|unfold bg_cost;lia]].
   apply bg_lap;first [exact sw1|exact sw2|exact sw3|reflexivity].
 - intros n w t. apply bg_fire;first [exact sw1|exact sw2|exact fw|reflexivity].
Qed.

Definition cbtrows_AST_79 : list (list (option Trans)) := [r_AST_79_0000].
Lemma cbt_AST_79_covers : Forall coversTr (map row_to_tm cbtrows_AST_79).
Proof. constructor;[exact cv_AST_79_0000|constructor]. Qed.
