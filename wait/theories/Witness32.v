(** Matching lower bounds for three-state binary waiting times.
    The finite checker excludes every earlier index in one computation. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement StatementTr CTape ClosureTr Size Bounds.
From SmallBB.Checkers Require Import Cycle.
From BBBWait Require Import Spec SpecTr.
Import ListNotations.

Definition state_delay_check tm B w q :=
  match csteps tm B c0 with
  | None => false
  | Some c => negb (cvisits tm c w q) &&
      match csteps tm w c with
      | None => false | Some d => st_eqb (fst d) q
      end
  end.

Definition instr_delay_check tm B w tg :=
  match csteps tm B c0 with
  | None => false
  | Some c => negb (cfires tm c w tg) &&
      match csteps tm w c with
      | None => false | Some d => instr_eqb (cinstr d) tg
      end
  end.

Lemma state_delay_sound : forall tm B w q,
  state_delay_check tm B w q = true ->
  VisitsAt tm q (B+w) /\
  forall t, B <= t -> t < B+w -> ~ VisitsAt tm q t.
Proof.
  intros tm B w q H; unfold state_delay_check in H.
  destruct (csteps tm B c0) as [c|] eqn:EB; [|discriminate].
  apply andb_prop in H as [Hsilent Hend]; apply negb_true_iff in Hsilent.
  destruct (csteps tm w c) as [d|] eqn:Ew; [|discriminate].
  apply st_eqb_spec in Hend; split.
  - exists (lift d); split; [|exact Hend].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, EB; exact Ew.
  - intros t Hlo Hhi Hv.
    destruct (visits_computable tm t q Hv) as (ct & Et & Hqt).
    destruct (csteps_prefix tm B t c0 ct Hlo Et) as (cb & Eb & Ebt).
    rewrite EB in Eb; injection Eb as <-.
    assert (Hyes : cvisits tm c w q = true).
    { exact (cvisits_complete tm w c q (t-B) ct ltac:(lia) Ebt Hqt). }
    rewrite Hyes in Hsilent; discriminate.
Qed.

Lemma instr_delay_sound : forall tm B w tg,
  instr_delay_check tm B w tg = true ->
  FiresAt tm tg (B+w) /\
  forall t, B <= t -> t < B+w -> ~ FiresAt tm tg t.
Proof.
  intros tm B w tg H; unfold instr_delay_check in H.
  destruct (csteps tm B c0) as [c|] eqn:EB; [|discriminate].
  apply andb_prop in H as [Hsilent Hend]; apply negb_true_iff in Hsilent.
  destruct (csteps tm w c) as [d|] eqn:Ew; [|discriminate].
  apply instr_eqb_spec in Hend; split.
  - exists (lift d); split; [|rewrite cinstr_lift; exact Hend].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, EB; exact Ew.
  - intros t Hlo Hhi Hv.
    destruct (fires_computable tm t tg Hv) as (ct & Et & Hqt).
    destruct (csteps_prefix tm B t c0 ct Hlo Et) as (cb & Eb & Ebt).
    rewrite EB in Eb; injection Eb as <-.
    assert (Hyes : cfires tm c w tg = true).
    { exact (cfires_complete tm w c tg (t-B) ct ltac:(lia) Ebt Hqt). }
    rewrite Hyes in Hsilent; discriminate.
Qed.

Theorem state_delay_minimal : forall ns ms tm B w q,
  Admissible ns ms tm -> state_delay_check tm B w q = true ->
  forall v, WaitBound ns ms B v -> w <= v.
Proof.
  intros ns ms tm B w q Had Hcheck v Hbound.
  destruct (state_delay_sound tm B w q Hcheck) as [Hend Hsilent].
  assert (Hfuture : FutureBeep tm q B).
  { exists (B+w); split; [lia|exact Hend]. }
  destruct (Hbound tm Had q Hfuture) as (t & Hlo & Hhi & Hv).
  destruct (le_lt_dec w v); [assumption|].
  exfalso; exact (Hsilent t Hlo ltac:(lia) Hv).
Qed.

Theorem instr_delay_minimal : forall ns ms tm B w tg,
  Admissible ns ms tm -> instr_delay_check tm B w tg = true ->
  forall v, WaitBoundTr ns ms B v -> w <= v.
Proof.
  intros ns ms tm B w tg Had Hcheck v Hbound.
  destruct (instr_delay_sound tm B w tg Hcheck) as [Hend Hsilent].
  assert (Hfuture : FutureBeepTr tm tg B).
  { exists (B+w); split; [lia|exact Hend]. }
  destruct (Hbound tm Had tg Hfuture) as (t & Hlo & Hhi & Hv).
  destruct (le_lt_dec w v); [assumption|].
  exfalso; exact (Hsilent t Hlo ltac:(lia) Hv).
Qed.

(** Right-hand form 1RB1LA_1RC1LB_1LA0RB, targeting state A. *)
Definition wait32_champion_state := machine_of_codes 3 2 [10;6;11;7;6;4].
Lemma wait32_champion_state_admissible : Admissible 3 2 wait32_champion_state.
Proof.
  split.
  - intros q s tr E; destruct q,s; cbn in E; try discriminate;
      injection E as <-; unfold output_ok; cbn; lia.
  - intros q s H; destruct q,s; cbn in H; try lia; reflexivity.
Qed.
Lemma wait32_state_checked : state_delay_check wait32_champion_state 55 38 StA = true.
Proof. vm_compute; reflexivity. Qed.
Theorem wait32_state_minimal : forall w, WaitBound 3 2 55 w -> 38 <= w.
Proof.
  eapply state_delay_minimal; [exact wait32_champion_state_admissible|exact wait32_state_checked].
Qed.

(** Right-hand form 1RB0LC_1LC0RA_1LA1LB, targeting instruction C1. *)
Definition wait32_champion_instr := machine_of_codes 3 2 [10;2;8;3;6;7].
Lemma wait32_champion_instr_admissible : Admissible 3 2 wait32_champion_instr.
Proof.
  split.
  - intros q s tr E; destruct q,s; cbn in E; try discriminate;
      injection E as <-; unfold output_ok; cbn; lia.
  - intros q s H; destruct q,s; cbn in H; try lia; reflexivity.
Qed.
Lemma wait32_instr_checked : instr_delay_check wait32_champion_instr 55 173 (StC,S1) = true.
Proof. vm_compute; reflexivity. Qed.
Theorem wait32_instr_minimal : forall w, WaitBoundTr 3 2 55 w -> 173 <= w.
Proof.
  eapply instr_delay_minimal; [exact wait32_champion_instr_admissible|exact wait32_instr_checked].
Qed.
