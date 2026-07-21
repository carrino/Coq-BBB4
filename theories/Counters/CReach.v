(** * CReach: reachability closure for the doubling counter families.

    The double_counter (#9/#30/#32/#37) and blockdbl (#11/#13/#28)
    laps are NESTED loops: an OUTER iteration of per-unit mini-sweeps
    whose phase counts vary with the iteration index (the comb
    collapse/spread, the accumulator re-shuttle).  A single parametric
    [csteps] run -- as [LapGlue] uses for the flat mono/spacer laps --
    does not describe them: the outer loop needs its own closer.

    [creach tm c c'] packages "[c'] is reachable from [c] in some
    number of steps".  It is a preorder ([creach_refl]/[creach_trans]),
    absorbs concrete runs ([creach_csteps]), and -- the key lemma --
    [creach_iter] folds a mid-configuration family [f : nat -> cconf]:
    if every adjacent pair [f i -> f (S i)] is reachable for [i < k],
    then [f 0 -> f k].  A double_counter macro-lap is then

        boundary prefix  ->  creach_iter over the k mini-sweeps  ->
        boundary suffix

    and [0 < n] for the [LapGlue] premise is recovered from the
    nonempty prefix phase chained in front (see [creach_pos]).

    No axioms (only [csteps_chain] from [WTape]). *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

Definition creach (tm : TM) (c c' : cconf) : Prop :=
  exists n, csteps tm n c = Some c'.

Lemma creach_refl : forall tm c, creach tm c c.
Proof. intros. exists 0. reflexivity. Qed.

Lemma creach_csteps : forall tm n c c',
  csteps tm n c = Some c' -> creach tm c c'.
Proof. intros tm n c c' H. exists n. exact H. Qed.

Lemma creach_trans : forall tm c1 c2 c3,
  creach tm c1 c2 -> creach tm c2 c3 -> creach tm c1 c3.
Proof.
  intros tm c1 c2 c3 (n1 & H1) (n2 & H2).
  exists (n1 + n2). eapply csteps_chain; eauto.
Qed.

(** The outer-loop closer: fold the mid-config family. *)
Lemma creach_iter : forall tm (f : nat -> cconf) k,
  (forall i, i < k -> creach tm (f i) (f (S i))) ->
  creach tm (f 0) (f k).
Proof.
  intros tm f k H. induction k as [| k IH].
  - apply creach_refl.
  - eapply creach_trans.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

(** A [creach] with a concrete [0 < n] witness, and the chaining that
    recovers it: any [creach] preceded by a strictly-positive concrete
    run yields the [LapGlue.Hlap]-shaped existential. *)
Lemma creach_pos : forall tm n c c1 c',
  csteps tm n c = Some c1 -> 0 < n ->
  creach tm c1 c' ->
  exists m, csteps tm m c = Some c' /\ 0 < m.
Proof.
  intros tm n c c1 c' Hpre Hn (n2 & H2).
  exists (n + n2). split; [| lia].
  eapply csteps_chain; eauto.
Qed.

(** Package [creach] into the [LapGlue.Hlap] existential (up to [lift],
    with the [0 < n] recovered from a positive prefix run). *)
Lemma creach_lap : forall tm n c c1 c' cnext,
  csteps tm n c = Some c1 -> 0 < n ->
  creach tm c1 c' ->
  lift c' = lift cnext ->
  exists m c'', csteps tm m c = Some c'' /\ lift c'' = lift cnext /\ 0 < m.
Proof.
  intros tm n c c1 c' cnext Hpre Hn Hreach Hlift.
  destruct (creach_pos tm n c c1 c' Hpre Hn Hreach) as (m & Hm & Hpos).
  exists m, c'. split; [exact Hm | split; [exact Hlift | exact Hpos]].
Qed.
