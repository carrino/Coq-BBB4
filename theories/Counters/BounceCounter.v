(** * BounceCounter: the working-area digit words (bounce_counter family).

    The two bounce_counter machines (#8, #33 -- BBB certs
    counter8/33) run a NESTED binary counter inside each macro-lap
    D(k) -> D(k+1): the stable sweep-configs carry a digit word after
    a 2-cell separator, each digit two equal cells ([Dw]), with a
    trailing accumulator.  One double-sweep is the cell-uniform
    binary increment

        1^j 0 x   -->   0^j 1 x

    on the word -- the C verifier's interior/overflow distinction is
    pure decode (the flipped top digit merges with the accumulator as
    cells), so a fixed-length bool word [w] tracks the whole
    macro-lap and the accumulator never moves.

    This file carries the word machinery driving the MeasureGlue
    composition: the carry view [bview], the measure [cval] (value of
    the pointwise complement, LSB first -- each increment decrements
    it by exactly one), and the digit-encoding and comb-rotation
    rewrites the sweep scripts consume. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape ILCounter ExpCounter.
Import ListNotations.

(** ** Digit encoding: one bit, two equal cells *)

Fixpoint Dw (w : list bool) : list Sym :=
  match w with
  | [] => []
  | true :: w' => S1 :: S1 :: Dw w'
  | false :: w' => S0 :: S0 :: Dw w'
  end.

Lemma Dw_app : forall u v, Dw (u ++ v) = Dw u ++ Dw v.
Proof.
  induction u as [|b u IH]; intros; simpl; [reflexivity|].
  destruct b; rewrite IH; reflexivity.
Qed.

Lemma Dw_true : forall j, Dw (repeat true j) = rep [S1; S1] j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.

Lemma Dw_false : forall j, Dw (repeat false j) = rep [S0; S0] j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.

(** ** The carry view on bool words *)

Fixpoint bview (w : list bool) : nat * option (list bool) :=
  match w with
  | [] => (0, None)
  | true :: w' => let '(j, r) := bview w' in (S j, r)
  | false :: w' => (0, Some w')
  end.

Lemma bview_some : forall w j x, bview w = (j, Some x) ->
  w = repeat true j ++ false :: x.
Proof.
  induction w as [|b w IH]; intros j x H; simpl in H.
  - discriminate.
  - destruct b.
    + destruct (bview w) as [j' r] eqn:E.
      inversion H; subst j r.
      simpl. rewrite <- (IH j' x eq_refl). reflexivity.
    + inversion H; subst j x. reflexivity.
Qed.

Lemma bview_none : forall w j, bview w = (j, None) ->
  w = repeat true j.
Proof.
  induction w as [|b w IH]; intros j H; simpl in H.
  - inversion H; subst j. reflexivity.
  - destruct b.
    + destruct (bview w) as [j' r] eqn:E.
      inversion H; subst j r.
      simpl. rewrite <- (IH j' eq_refl). reflexivity.
    + discriminate.
Qed.

(** ** The measure: value of the complement, LSB first *)

Fixpoint cval (w : list bool) : nat :=
  match w with
  | [] => 0
  | b :: w' => (if b then 0 else 1) + 2 * cval w'
  end.

(** One increment decrements the measure by exactly one. *)
Lemma cval_step : forall j x,
  S (cval (repeat false j ++ true :: x)) = cval (repeat true j ++ false :: x).
Proof.
  induction j; intros x; simpl.
  - lia.
  - rewrite <- (IHj x). lia.
Qed.

Lemma cval_false : forall n, S (cval (repeat false n)) = 2 ^ n.
Proof.
  induction n; simpl; lia.
Qed.

Lemma cval_true : forall n, cval (repeat true n) = 0.
Proof.
  induction n; simpl; lia.
Qed.

(** The increment preserves word length. *)
Lemma len_step : forall j (x : list bool),
  length (repeat false j ++ true :: x) = length (repeat true j ++ false :: x).
Proof.
  intros. rewrite !app_length, !repeat_length. reflexivity.
Qed.

(** An odd solid run splits into pairs and a lone cell. *)
Lemma solid_split : forall q,
  rep [S1] (S (2 * q)) = rep [S1; S1] q ++ [S1].
Proof.
  induction q.
  - reflexivity.
  - replace (2 * S q) with (S (S (2 * q))) by lia.
    cbn [rep app].
    rewrite <- IHq.
    reflexivity.
Qed.

(** Pairs and a lone triple fuse into an odd solid run. *)
Lemma ones_fold3 : forall q,
  rep [S1; S1] q ++ [S1; S1; S1] = rep [S1] (S (S (S (2 * q)))).
Proof.
  intros.
  rewrite rep_dbl, rep1_fold, rep1_fold, rep1_fold, app_nil_r.
  reflexivity.
Qed.

(** ** Comb rotations (the (xy)-phase changes of a bounce sweep) *)

Lemma comb_rot0 : forall (x y : Sym) k Y,
  x :: rep [y; x] k ++ Y = rep [x; y] k ++ x :: Y.
Proof.
  intros.
  change (x :: rep [y; x] k ++ Y) with ((x :: rep [y; x] k) ++ Y).
  change (y :: x :: nil) with ([y] ++ [x]).
  rewrite rep_rot, <- app_assoc.
  reflexivity.
Qed.

Lemma comb_rot1 : forall (x y : Sym) k Y,
  x :: rep [y; x] k ++ y :: Y = rep [x; y] (S k) ++ Y.
Proof.
  intros. rewrite comb_rot0, pair_fold. reflexivity.
Qed.
