(** * ValueLapTr: positive laps over an arbitrary changing value.

    Some counters are most naturally described by a word transducer,
    rather than a positional numeral.  An anchor [Cf n x] can combine
    such a value [x] with a sweep parameter [n].  Each positive lap
    increments [n] and replaces [x] by [next x].  No ordering or
    arithmetic interpretation of [x] is required: positivity of the
    lap lengths puts anchors at unbounded execution indices.

    The direct theorem requires every instruction to be reachable from
    every anchor.  The wrapped theorem permits a list of instructions
    which never fire, with the same halt-redirect argument as LapGlueTr.
    Lap endpoints are compared after [lift], permitting blank padding. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.

Section ValueIteration.

Variable V : Type.
Variable next : V -> V.

Fixpoint value_lap_iter (n : nat) (x : V) : V :=
  match n with
  | O => x
  | S k => next (value_lap_iter k x)
  end.

End ValueIteration.

Section ValueLap.

Variable tm : TM.
Variable V : Type.
Variable next : V -> V.
Variable Cf : nat -> V -> cconf.
Variable x0 : V.

Hypothesis Hboot : exists t0,
  stepn tm t0 InitES = Some (lift (Cf 0 x0)).
Hypothesis Hlap : forall n x, exists k c',
  csteps tm k (Cf n x) = Some c' /\
  lift c' = lift (Cf (S n) (next x)) /\ 0 < k.

(** The [n]-th anchor is reached no earlier than execution index [n]. *)
Lemma value_lap_reach : forall n, exists T, n <= T /\
  stepn tm T InitES = Some (lift (Cf n (value_lap_iter V next n x0))).
Proof.
  induction n as [|n IH].
  - destruct Hboot as (t0 & H0).
    exists t0. split; [lia | exact H0].
  - destruct IH as (T & HT & Hstep).
    destruct (Hlap n (value_lap_iter V next n x0))
      as (k & c' & Hrun & Hlift & Hk).
    exists (T + k). split; [lia|].
    rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Lemma value_lap_nonhalt : forall n, stepn tm n InitES <> None.
Proof.
  intro n.
  destruct (value_lap_reach n) as (T & HT & Hstep).
  destruct (stepn_prefix tm n T InitES _ HT Hstep) as (c & Hc & _).
  rewrite Hc. discriminate.
Qed.

Hypothesis Hfire : forall n x t, exists k c,
  csteps tm k (Cf n x) = Some c /\ cinstr c = t.

Theorem value_lap_neverqhtr : NeverQuasiHaltsTr tm.
Proof.
  intros t _ N.
  destruct (value_lap_reach N) as (T & HT & Hstep).
  destruct (Hfire N (value_lap_iter V next N x0) t)
    as (k & c & Hrun & Ht).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hrun.
  - rewrite cinstr_lift. exact Ht.
Qed.

End ValueLap.

Section WrappedValueLap.

Variable tm : TM.
Variable pins : list Instr.
Variable V : Type.
Variable next : V -> V.
Variable Cf : nat -> V -> cconf.
Variable x0 : V.

Hypothesis Hboot : exists t0,
  stepn (tm_wrap_trs tm pins) t0 InitES = Some (lift (Cf 0 x0)).
Hypothesis Hlap : forall n x, exists k c',
  csteps (tm_wrap_trs tm pins) k (Cf n x) = Some c' /\
  lift c' = lift (Cf (S n) (next x)) /\ 0 < k.
Hypothesis Hfire : forall t, ~ In t pins -> forall n x, exists k c,
  csteps (tm_wrap_trs tm pins) k (Cf n x) = Some c /\ cinstr c = t.

Theorem value_lap_wrap_neverqhtr : NeverQuasiHaltsTr tm.
Proof.
  intros t (n0 & c0 & Hc0 & Ht0) N.
  pose proof (wrap_trs_agree tm pins InitES
    (value_lap_nonhalt (tm_wrap_trs tm pins) V next Cf x0 Hboot Hlap))
    as Hagree.
  assert (Hnp : ~ In t pins).
  { destruct (Hagree n0) as [_ Hnot]. rewrite <- Ht0.
    exact (Hnot c0 Hc0). }
  destruct (value_lap_reach (tm_wrap_trs tm pins) V next Cf x0 Hboot Hlap N)
    as (T & HT & Hstep).
  destruct (Hfire t Hnp N (value_lap_iter V next N x0))
    as (k & c & Hrun & Ht).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - destruct (Hagree (T + k)) as [Heq _]. rewrite <- Heq.
    rewrite stepn_add, Hstep. apply csteps_lift; exact Hrun.
  - rewrite cinstr_lift. exact Ht.
Qed.

End WrappedValueLap.
