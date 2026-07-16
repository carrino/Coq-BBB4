(** * ILCounter: the interleaved counter encoding (interleave_counter family).

    The two interleave_counter machines (#18, #35 -- BBB certs
    counter18/35) keep the counter n on the LEFT of a growing
    (110)-comb, encoded as E(n): with m = bit_length(n), E(n) has
    length 2m-1, a 1 at every even offset and the low m-1 bits of n
    (MSB-first) at the odd offsets.  On the cconf left list (nearest
    cell first) that region reads LSB-first:

      rev (E n) = 1 b0 1 b1 ... 1 b_{m-2} 1,

    which is exactly the positive-recursion [Ip] below (each low bit
    contributes an interleave 1 and itself; the terminating [xH] is
    E's leading 1).  Same carry view [cview] as the other families
    (MonoCounter), new decomposition lemmas:

    - interior carry (cview p = (j, Some q)): j set low bits under a
      clear bit -- the [S1;S1] pairs flip to [S1;S0] and the stop pair
      [S1;S0] flips to [S1;S1];
    - overflow (cview p = (S j, None), p = 2^(j+1) - 1): the whole
      region is pairs of ones and the increment appends a fresh
      most-significant [S1] pair beyond the old tape edge. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** [Ip p] = rev (E p): LSB-first interleaved bits, one [S1] pad per
    bit, closed by the leading-1 cell. *)
Fixpoint Ip (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => S1 :: S0 :: Ip q
  | xI q => S1 :: S1 :: Ip q
  end.

Lemma Ip_head : forall p, exists w, Ip p = S1 :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma cview_some_I : forall p j q, cview p = (j, Some q) ->
  Ip p = rep [S1; S1] j ++ S1 :: S0 :: Ip q /\
  Ip (Pos.succ p) = rep [S1; S0] j ++ S1 :: S1 :: Ip q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_I : forall p j, cview p = (S j, None) ->
  Ip p = rep [S1; S1] j ++ [S1] /\
  Ip (Pos.succ p) = rep [S1; S0] (S j) ++ [S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j' r.
    destruct j as [|j].
    + (* cview p = (0, None) is impossible *)
      exfalso. destruct p; simpl in E.
      * destruct (cview p) as [j r]; discriminate.
      * discriminate.
      * discriminate.
    + destruct (IHp j eq_refl) as (H1 & H2).
      split; simpl.
      * rewrite H1. reflexivity.
      * rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** The recross pair fold: a fresh pair fuses onto a pair run. *)
Lemma pair_fold : forall (x y : Sym) j X,
  rep [x; y] j ++ x :: y :: X = rep [x; y] (S j) ++ X.
Proof.
  intros.
  replace (S j) with (j + 1) by lia.
  rewrite rep_add.
  cbn [rep app].
  rewrite <- app_assoc.
  reflexivity.
Qed.
