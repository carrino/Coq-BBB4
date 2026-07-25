(** * DpCounter: the DOUBLED-BIT interleave encoding.

    A third counter encoding for the wave-9 residue, alongside
    [ILCounter.Ip] and [JpCounter.Jp].

    [Ip] and [Jp] put a MARKER cell between consecutive data bits
    ([Ip p = 1 b0 1 b1 ... 1], markers always [S1]).  This family instead
    writes each bit TWICE:

      Dp p = b0 b0 b1 b1 ... bk bk        (LSB nearest the head)

    so there are no marker cells at all -- the "markers" are the data.
    That is exactly why the wave-8/wave-9 recognizers never saw these
    machines: every one of them decodes a candidate tape by checking that
    the cells at one parity ALL hold [S1], and in a doubled-bit tape those
    cells are the data bits, so any counter value with a clear bit is
    rejected and the machine is reported as having no anchor family at all.

    Found by a human read of [1RB1RD_1LC0LB_1RA1LC_0RD1LB] -- "right wall
    and 2 copies of each bit" -- and confirmed by simulation: at the anchor
    the decode marches 1, 2, 3, ..., 7503 with no gaps, and both lap
    branches are affine (interior 4 + 4j, overflow 4 + 4j), which is what
    the single-sweep board template needs.

    The recursion is [Ip]'s with the marker replaced by a copy of the bit,
    so the decomposition lemmas have the same shape and the same proofs.
    Note [Dp]'s terminating [xH] contributes TWO cells, which makes the
    overflow statement slightly cleaner than [ILCounter]'s: the all-ones
    region is exactly [rep [S1;S1] (S j)] with no trailing odd cell.

    Axiom footprint: none (Closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** [Dp p]: every bit of [p] doubled, least significant nearest the head,
    the leading 1 included (so [Dp p] always has even length). *)
Fixpoint Dp (p : positive) : list Sym :=
  match p with
  | xH => [S1; S1]
  | xO q => S0 :: S0 :: Dp q
  | xI q => S1 :: S1 :: Dp q
  end.

Lemma Dp_pair : forall p, exists x w, Dp p = x :: x :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma Dp_even : forall p, Nat.Even (length (Dp p)).
Proof.
  induction p; simpl; try (destruct IHp as [k Hk]; exists (S k); lia).
  exists 1. reflexivity.
Qed.

(** Interior carry: [j] set low bits under a clear bit.  The [S1] pairs
    flip to [S0] pairs and the stop pair [S0;S0] flips to [S1;S1]. *)
Lemma cview_some_D : forall p j q, cview p = (j, Some q) ->
  Dp p = rep [S1; S1] j ++ S0 :: S0 :: Dp q /\
  Dp (Pos.succ p) = rep [S0; S0] j ++ S1 :: S1 :: Dp q.
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

(** Overflow: [p = 2^(j+1) - 1], the whole region is [S1] pairs and the
    increment clears them all and appends a fresh most-significant pair
    beyond the old tape edge. *)
Lemma cview_none_D : forall p j, cview p = (S j, None) ->
  Dp p = rep [S1; S1] (S j) /\
  Dp (Pos.succ p) = rep [S0; S0] (S j) ++ [S1; S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j' r.
    destruct j as [|j].
    + (* cview p = (0, None) is impossible *)
      exfalso. destruct p; simpl in E.
      * destruct (cview p) as [jj rr]; discriminate.
      * discriminate.
      * discriminate.
    + destruct (IHp j eq_refl) as (H1 & H2).
      split; simpl.
      * rewrite H1. reflexivity.
      * rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** The all-ones region folds into a single run of [S1], which is what the
    board's ripple/return cycles consume one CELL at a time (these machines
    sweep cell-by-cell, not pair-by-pair). *)
Lemma Dp_ones_run : forall j, rep [S1; S1] j = rep [S1] (2 * j).
Proof. intro j. apply rep_dbl. Qed.

Lemma Dp_zeros_run : forall j, rep [S0; S0] j = rep [S0] (2 * j).
Proof. intro j. apply rep_dbl. Qed.
