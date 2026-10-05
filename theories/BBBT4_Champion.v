(** * BBBT4_Champion: the champion attains 32,779,478 at instruction level.

      [champion_quiet_after_D0 : QuietAfterTr tm_champion (StD, S0) 32779477]
      [champion_attains_tr     : AttainsTr tm_champion champion_score]

    The lower bound of [BBBT4_statement] (BBBT4_Spec.v).  It reuses the state proof:
    the state-level champion file already pins the configuration at
    index 32,779,477 in state [StD] ([visits_D_prev], a [vm_compute]
    over binary fuel) and shows no state but [StC] is entered from
    index 32,779,478 on ([not_visits_other]).  The instruction the
    machine is about to fire at 32,779,477 is [(StD, a)] for the symbol
    [a] under the head; one more binary-fuel [vm_compute]
    ([prev_instr_N], the same ~9 s run as [prev_run_N]) pins [a = S0].
    It is never fired again, because firing it means entering [StD]
    ([fires_visits]).  So instruction (D, 0) last fires at 32,779,477
    and its score is exactly [champion_score].

    Also [champion_quasihalts_tr] and the matching tightness
    [qhboundtr_champion_tight]: no [B] below [champion_score] satisfies
    [QHBoundTr B tm_champion]. *)

From Coq Require Import Arith Lia Bool NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec BBBT4_Spec CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.

(** One step before the landing the machine is in [StD] reading [S0]:
    the instruction about to fire is (D, 0). *)
Lemma prev_instr_N :
  match cstepsN tm_champion champ_prevN c0 with
  | Some (q, (_, h, _)) => st_eqb q StD && sym_eqb h S0
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fires_D0_prev : FiresAt tm_champion (StD, S0) champ_prev.
Proof.
  pose proof prev_instr_N as H.
  rewrite cstepsN_nat, champ_prevN_nat in H.
  destruct (csteps tm_champion champ_prev c0) as [[q [[l h] r]]|] eqn:Eq;
    [| discriminate].
  apply andb_prop in H as [Hq Hh].
  apply st_eqb_spec in Hq. apply sym_eqb_spec in Hh. subst q h.
  exists (lift (StD, (l, S0, r))). split.
  - rewrite <- lift_c0. exact (csteps_lift _ _ _ _ Eq).
  - reflexivity.
Qed.

(** (D, 0) fires at 32,779,477 and never afterwards: firing it means
    entering [StD], and only [StC] is entered from 32,779,478 on. *)
Theorem champion_quiet_after_D0 : QuietAfterTr tm_champion (StD, S0) champ_prev.
Proof.
  split; [exact fires_D0_prev |].
  intros n Hn Hfn.
  apply (not_visits_other StD n); [discriminate | | exact (fires_visits _ _ _ _ Hfn)].
  rewrite <- champ_prev_S. exact Hn.
Qed.

(** The lower bound, in the spec's vocabulary. *)
Theorem champion_attains_tr : AttainsTr tm_champion champion_score.
Proof.
  exists (StD, S0), champ_prev.
  split; [exact champion_quiet_after_D0 | exact champ_prev_S].
Qed.

Theorem champion_quasihalts_tr : QuasiHaltsTr tm_champion.
Proof. exact (attains_tr_qh _ _ champion_attains_tr). Qed.

(** No bound below the champion's score bounds the champion at
    instruction level. *)
Theorem qhboundtr_champion_tight : forall B,
  QHBoundTr B tm_champion -> champion_score <= B.
Proof.
  intros B H.
  rewrite <- champ_prev_S.
  exact (H (StD, S0) champ_prev champion_quiet_after_D0).
Qed.

Print Assumptions champion_attains_tr.
