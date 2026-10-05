(** * BBBT4_Champion: the champion attains 32,779,478 at instruction level.

      [champion_attains_tr : AttainsTr tm_champion champion_score]

    The lower bound of [BBBT4_statement] (BBBT4_Spec.v).  No new run:
    the state-level champion file already pins the configuration at
    index 32,779,477 in state [StD] ([visits_D_prev], a [vm_compute]
    over binary fuel) and shows no state but [StC] is entered from
    index 32,779,478 on ([not_visits_other]).  The instruction the
    machine is about to fire at 32,779,477 is [(StD, a)] for the symbol
    [a] under the head ([visits_fires]); it is never fired again,
    because firing it means entering [StD] ([fires_visits]).  So its
    last fire is at 32,779,477 and its score is exactly
    [champion_score].

    Also [champion_quasihalts_tr] and the matching tightness
    [qhboundtr_champion_tight]: no [B] below [champion_score] satisfies
    [QHBoundTr B tm_champion]. *)

From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec BBBT4_Spec.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.

(** state [StD]'s last visit, read as an instruction: some [(StD, a)]
    fires at 32,779,477 and never afterwards. *)
Theorem champion_quiet_after_tr :
  exists a, QuietAfterTr tm_champion (StD, a) champ_prev.
Proof.
  destruct (proj1 (visits_fires tm_champion StD champ_prev) visits_D_prev)
    as (a & Hf).
  exists a. split; [exact Hf |].
  intros n Hn Hfn.
  apply (not_visits_other StD n); [discriminate | | exact (fires_visits _ _ _ _ Hfn)].
  rewrite <- champ_prev_S. exact Hn.
Qed.

(** The lower bound, in the spec's vocabulary. *)
Theorem champion_attains_tr : AttainsTr tm_champion champion_score.
Proof.
  destruct champion_quiet_after_tr as (a & Hq).
  exists (StD, a), champ_prev.
  split; [exact Hq | exact champ_prev_S].
Qed.

Theorem champion_quasihalts_tr : QuasiHaltsTr tm_champion.
Proof. exact (attains_tr_qh _ _ champion_attains_tr). Qed.

(** No bound below the champion's score bounds the champion at
    instruction level. *)
Theorem qhboundtr_champion_tight : forall B,
  QHBoundTr B tm_champion -> champion_score <= B.
Proof.
  intros B H.
  destruct champion_quiet_after_tr as (a & Hq).
  rewrite <- champ_prev_S.
  exact (H (StD, a) champ_prev Hq).
Qed.

Print Assumptions champion_attains_tr.
