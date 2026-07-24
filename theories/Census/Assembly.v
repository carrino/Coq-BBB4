(** * Census/Assembly: the endgame composition for the BBB(4) upper bound.

    The census theorem ([census_decided], certified 2026-07-24 at
    [D_census] = 5,156) has the shape

      forall tm, QHBound 2000 tm \/ Deferred D tm.

    This file provides the OTHER half of the final argument: once every
    machine in the deferred list [D] carries a per-machine theorem
    [NonHalt tm /\ QHBound B' tm] (for the eventual bound
    [B' = BBB(4) champion score + 1]), the two compose into the global
    upper bound

      forall tm, QHBound B' tm.

    The load-bearing content is [deferred_qhbound]: the [Deferred]
    orbit (don't-care completion, non-start state swaps, mirroring) was
    designed so that semantic properties proven for the base list lift
    to the whole orbit -- here we cash that in for [NonHalt /\ QHBound],
    using only the existing transfer lemmas ([nonhalt_le]/[qhbound_le],
    [quiet_swap], [qhbound_mirror]/[mirror_nonhalt]).

    Two practical consequences:

    - The census walk at B = 2000 never has to be re-run for the
      endgame: the remaining work is the [Forall] over the FROZEN
      5,156-row [D_census], accumulated as ordinary per-machine
      theorems (never-QH machines give both conjuncts via
      [neverqh_qhbound]/[never_qh_nonhalt]; quasihalters need their
      quiet profile bounded by B').
    - [census_decided] enters as a section hypothesis, so this file
      compiles without loading the census [.vo]; the final instantiation
      ([all_qhbound _ _ HB census_decided HD]) is a one-liner wherever
      the census and the completed [Forall] are both in scope.

    NOTE the achievability half of BBB(4) (some machine ATTAINS the
    champion score) is a separate per-machine exact-score theorem; this
    file only assembles the upper bound. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

(** ** Reverse-direction transfer helpers

    The [Deferred] induction consumes the orbit constructors from the
    inside out: the hypothesis is about the transformed machine, the
    goal about the original.  [quiet_swap] is an iff and [St_swap] is
    an involution ([St_swap_swap]), so the reverse directions are
    free. *)

Lemma qhbound_unswap : forall u v B tm,
  u <> StA -> v <> StA ->
  QHBound B (TM_swap u v tm) -> QHBound B tm.
Proof.
  intros u v B tm HuA HvA H q s Hq.
  apply (H (St_swap u v q) s).
  apply (quiet_swap u v tm (St_swap u v q) s HuA HvA).
  rewrite St_swap_swap. exact Hq.
Qed.

Lemma nonhalt_unswap : forall u v tm,
  u <> StA -> v <> StA ->
  NonHalt (TM_swap u v tm) -> NonHalt tm.
Proof.
  intros u v tm HuA HvA H n E.
  apply (H n).
  rewrite stepn_swap, es_swap_init by assumption.
  rewrite E. reflexivity.
Qed.

(** ** The orbit lift: per-machine facts on [D] cover all of [Deferred D] *)

Lemma deferred_qhbound : forall (D : list TM) (B : nat),
  Forall (fun tm => NonHalt tm /\ QHBound B tm) D ->
  forall tm, Deferred D tm -> NonHalt tm /\ QHBound B tm.
Proof.
  intros D B HD tm Hdef.
  induction Hdef as [h tm Hin Hle
                    | u v tm Huv HuA HvA Hdef IH
                    | tm Hdef IH].
  - rewrite Forall_forall in HD.
    destruct (HD h Hin) as [Hnh Hqb].
    split.
    + exact (nonhalt_le h tm Hnh Hle).
    + exact (qhbound_le B h tm Hnh Hqb Hle).
  - destruct IH as [Hnh Hqb]. split.
    + exact (nonhalt_unswap u v tm HuA HvA Hnh).
    + exact (qhbound_unswap u v B tm HuA HvA Hqb).
  - destruct IH as [Hnh Hqb]. split.
    + exact (mirror_nonhalt tm Hnh).
    + exact (qhbound_mirror B tm Hqb).
Qed.

(** ** The composition *)

Section Endgame.
  Variable D : list TM.        (** the frozen deferred list *)
  Variable B' : nat.           (** the final bound (champion score + 1) *)
  Hypothesis HB : 2000 <= B'.
  Hypothesis census : forall tm, QHBound 2000 tm \/ Deferred D tm.
  Hypothesis HD : Forall (fun tm => NonHalt tm /\ QHBound B' tm) D.

  Theorem all_qhbound : forall tm, QHBound B' tm.
  Proof.
    intros tm.
    destruct (census tm) as [H | H].
    - exact (qhbound_mono 2000 B' tm HB H).
    - exact (proj2 (deferred_qhbound D B' HD tm H)).
  Qed.
End Endgame.
