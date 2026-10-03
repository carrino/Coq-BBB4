(** * Counters.AbsStepTr: a board on an ABSTRACT step function
    (SCOPING_INSTR 7.4.LE9).

    The LE9 boards ([TopMapTr], [TopMapGTr], ...) fix the shape of the
    abstract state: one binary counter and a small state beside it.  LE7's
    out-of-step mirrors hold TWO binary counters, one each side of a pivot
    cell, incremented in turn, and their tops fall at different times.  So
    here the abstract state is any type [St], the configuration any [C],
    the round any function [F] that preserves an invariant [I]:

      - [Hstep]: from [C s], the machine reaches [C (F s)] in >= 1 steps;
      - [Hfire]: from every invariant state, some later round fires each
        unpinned instruction.

    A row proves [Hstep] by composing one-sided arms (each counter's carry
    over [j] ones, with the other side an opaque tail) and [Hfire] on the
    dynamics of [F] by hand.  Never-QH closer.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderCheckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import NestCountTr.
Import ListNotations.

Section AbsStep.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable St : Type.
Variable C  : St -> cconf.
Variable F  : St -> St.
Variable I  : St -> Prop.

Fixpoint fiter (n : nat) (s : St) : St :=
  match n with 0 => s | S n' => fiter n' (F s) end.

Lemma fiter_add : forall n1 n2 s, fiter (n1 + n2) s = fiter n2 (fiter n1 s).
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Lemma fiter_S : forall n s, fiter (S n) s = F (fiter n s).
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite fiter_add. reflexivity.
Qed.

Hypothesis HI : forall s, I s -> I (F s).
Hypothesis Hstep : forall s, I s -> Reach1 tm (C s) (C (F s)).
Hypothesis Hfire : forall t, ~ In t pins -> forall s, I s ->
  exists n, Fires tm (C (fiter n s)) t.

Lemma fiter_inv : forall n s, I s -> I (fiter n s).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, HI, Hs. Qed.

Variable s0 : St.
Hypothesis Hinv0 : I s0.

Definition aCf (n : nat) : cconf := C (fiter n s0).

Lemma aCf_lap : forall n, exists k c',
  csteps tm k (aCf n) = Some c' /\ lift c' = lift (aCf (S n)) /\ 0 < k.
Proof.
  intros n.
  pose proof (fiter_inv n s0 Hinv0) as Hi.
  destruct (reach1_csteps tm _ _ (Hstep _ Hi)) as (k & c' & Hk & Hc & Hl).
  exists k, c'. unfold aCf. rewrite fiter_S.
  split; [exact Hc | split; [exact Hl | exact Hk]].
Qed.

Lemma aCf_fire : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (aCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp (fiter N s0) (fiter_inv N s0 Hinv0)) as (n & k & c' & Hc & Ht).
  exists (N + n), k, c'. split; [lia|].
  unfold aCf. rewrite fiter_add. split; assumption.
Qed.

Theorem absstep_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (C s0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins aCf).
  - exists t0. exact Hboot.
  - exact aCf_lap.
  - intros t Hnp N. exact (aCf_fire t N Hnp).
Qed.

End AbsStep.
