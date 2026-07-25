(** * KpCounter: the PLAIN binary counter encoding (no markers at all).

    The fourth counter encoding, alongside [ILCounter.Ip], [JpCounter.Jp]
    (marker between bits) and [DpCounter.Dp] (each bit doubled).  Here there
    is nothing between the bits -- the tape word IS the base-2 expansion:

      Kp p = b0 b1 ... bk        (LSB nearest the head, MSB deepest)

    Human read of [1RB0LD_0LC1LA_0RC1LA_1RC0LD]: "wall on the right, msb on
    the left, normal counter."  Read in true tape order, MSB leftmost, that is
    exactly this; read nearest-first from a head sitting at the RIGHT end it
    is LSB-first, which is the orientation below.  The wall is the far side of
    the anchor, not part of the word.

    This is the single largest family in the residue -- the merged
    `tools/counter_encodings.tsv` classifies 375 machines as `KCOPY1`, i.e.
    one cell per bit -- and it had no Coq encoding because every recognizer
    here was built around a marker cell that this family does not have.

    Note how much simpler the decomposition is than the interleaved families:
    there is no marker to preserve, so the carry run is a run of [S1] cells
    and the increment simply clears it and sets the next cell.

    Axiom footprint: none (Closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

Fixpoint Kp (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => S0 :: Kp q
  | xI q => S1 :: Kp q
  end.

Lemma Kp_nonnil : forall p, exists x w, Kp p = x :: w.
Proof. destruct p; simpl; eauto. Qed.

(** Interior carry: [j] set low bits under a clear bit.  The run of [S1]
    clears and the stop bit sets. *)
Lemma cview_some_K : forall p j q, cview p = (j, Some q) ->
  Kp p = rep [S1] j ++ S0 :: Kp q /\
  Kp (Pos.succ p) = rep [S0] j ++ S1 :: Kp q.
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

(** Overflow: [p = 2^(j+1) - 1] is a solid run of [S1]; the increment clears
    it and appends a fresh most-significant [S1] beyond the old tape edge. *)
Lemma cview_none_K : forall p j, cview p = (S j, None) ->
  Kp p = rep [S1] (S j) /\
  Kp (Pos.succ p) = rep [S0] (S j) ++ [S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j' r.
    destruct j as [|j].
    + exfalso. destruct p; simpl in E.
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
