(** A certificate for a shorter observation window also certifies every
    longer window at the same BBB cutoff. *)
From Coq Require Import Arith Lia.
From BBBWait Require Import Spec SpecTr.

Lemma state_wait_monotone : forall tm B w v, w <= v ->
  (forall q, FutureBeep tm q B -> BeepWindow tm q B w) ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B v.
Proof.
  intros tm B w v Hle H q Hf.
  destruct (H q Hf) as (t & Ht & Htw & Hv).
  exists t; repeat split; try assumption; lia.
Qed.

Lemma instr_wait_monotone : forall tm B w v, w <= v ->
  (forall q, FutureBeepTr tm q B -> BeepWindowTr tm q B w) ->
  forall q, FutureBeepTr tm q B -> BeepWindowTr tm q B v.
Proof.
  intros tm B w v Hle H q Hf.
  destruct (H q Hf) as (t & Ht & Htw & Hv).
  exists t; repeat split; try assumption; lia.
Qed.
