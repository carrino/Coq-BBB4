(** * GpCounter: the GRAY-CODE counter encoding.

    The sixth counter word family, alongside [ILCounter.Ip] /
    [JpCounter.Jp] (marker BEFORE each bit), [KpCounter.Kp] (no marker),
    [DpCounter.Dp] (each bit doubled) and [MpCounter.Mp] (marker AFTER
    each bit).  Those five all encode the BINARY expansion of the count and
    differ only in the digit alphabet; this one does not.  Here the tape
    word is the REFLECTED BINARY (Gray) code, which is a different function
    of the count, so it needs its own fixpoint and its own decomposition
    lemmas -- but, as [cview_some_G] / [cview_none_G] below show, the same
    carry view [MonoCounter.cview] and the same AFFINE shape that
    [Checkers/LapDecider.v] already expresses.

    Human read of [0RB0LA_0RC1RC_1LD0LD_1LA1RB] (WAVE13_FINDINGS.md 9d):
    "some bits seem inverted, or maybe it counts up and down before doing a
    carry", refined by "when it carries the msb it keeps the top 2 bits set:
    12 -> 15 -> 9, then 24 -> 31 -> 17, then 48 -> 63 -> 33" -- which is
    exactly g(2^k) = 2^k + 2^(k-1).

    The measured anchor word of that machine, read nearest-cell-first, is
    the Gray code of TWICE the lap index:

      Gp p = bits (gray (2 p))   LSB-first, MSB deepest

    (verified against the raw simulator for p = 1 .. 19999 before this file
    was written).  The doubling is not a quirk of the encoding: the machine
    passes through every Gray word, and its two anchor states catch the even
    and the odd ones respectively, so the family indexed by ONE state steps
    by two.  Taking the even family makes [Pos.succ] the right successor and
    [LapGlue] applies unchanged.

    Structurally, [gray (2 p)] is [lowbit p :: gray p], and
    [gray (2 q + 1)] flips the low cell of [gray (2 q)] -- which is the
    whole content of the fixpoint below, with no [lowbit] function needed.

    Axiom footprint: none (closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** Flip one cell.  The Gray increment's whole effect on the high part. *)
Definition negs (s : Sym) : Sym := match s with S0 => S1 | S1 => S0 end.

Lemma negs_invol : forall s, negs (negs s) = s.
Proof. destruct s; reflexivity. Qed.

(** Flip the LOW cell of a word (the words here are never empty). *)
Definition flip0 (w : list Sym) : list Sym :=
  match w with [] => [] | x :: r => negs x :: r end.

(** The anchor word.  [Gp p = bits (gray (2p))], LSB nearest the head. *)
Fixpoint Gp (p : positive) : list Sym :=
  match p with
  | xH => [S1; S1]
  | xO q => S0 :: Gp q
  | xI q => S1 :: flip0 (Gp q)
  end.

(** Every word is non-empty, so its low cell and high part always split.
    This is what lets the interior branch be stated with the flipped cell
    [x] made CONCRETE (see the two-sub-case split in the emitter): the
    opaque tail [G] is then the same on both sides of the lap, which is
    exactly what [LapDecider.srun_sound] requires. *)
Lemma Gp_shape : forall p, exists x G, Gp p = x :: G.
Proof. destruct p; simpl; eauto. Qed.

Lemma flip0_cons : forall x G, flip0 (x :: G) = negs x :: G.
Proof. reflexivity. Qed.

(** ** The decomposition lemmas the lap templates consume *)

(** Interior increment with a NON-EMPTY carry run ([j+1] trailing set bits).
    One repeated block [rep [S0] j], one flipped cell, and an opaque tail
    [G] shared by source and target -- the AFFINE shape.

    Reading it: the source opens [S1] because [p] is odd, the target opens
    [S0] because [Pos.succ p] is even, and the carry run itself is the
    [rep [S0] j] both sides share. *)
Lemma cview_some_G : forall p j q x G,
  cview p = (S j, Some q) -> Gp q = x :: G ->
  Gp p = S1 :: rep [S0] j ++ S1 :: x :: G /\
  Gp (Pos.succ p) = S0 :: rep [S0] j ++ S1 :: negs x :: G.
Proof.
  induction p; intros j q x G H HG; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    + (* p itself has a single trailing one: cview p = (0, Some q) *)
      destruct p as [p'|p'|]; simpl in E; try discriminate.
      * destruct (cview p'); discriminate.
      * inversion E; subst q. simpl. rewrite HG. split; reflexivity.
    + destruct (IHp j q x G eq_refl HG) as (H1 & H2).
      simpl. rewrite H1, H2. split; reflexivity.
  - discriminate.
  - discriminate.
Qed.

(** Interior increment with an EMPTY carry run: the two words differ in
    their two low cells only. *)
Lemma cview_some0_G : forall p q x G,
  cview p = (0, Some q) -> Gp q = x :: G ->
  Gp p = S0 :: x :: G /\ Gp (Pos.succ p) = S1 :: negs x :: G.
Proof.
  intros p q x G H HG. destruct p as [p'|p'|]; simpl in H.
  - destruct (cview p'); discriminate.
  - inversion H; subst q. simpl. rewrite HG. split; reflexivity.
  - discriminate.
Qed.

(** Overflow, [p = 2^(j+1) - 1].  The Gray word of an all-ones count is a
    single low [S1] over a clear run; the increment moves that [S1] one
    cell deeper and keeps the new msb set -- John's "when it carries the
    msb it keeps the top 2 bits set". *)
Lemma cview_none_G : forall p j, cview p = (S j, None) ->
  Gp p = S1 :: rep [S0] j ++ [S1] /\
  Gp (Pos.succ p) = S0 :: rep [S0] j ++ [S1; S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    + (* cview p = (0, None) is impossible *)
      exfalso. destruct p; simpl in E.
      * destruct (cview p) as [jj rr]; discriminate.
      * discriminate.
      * discriminate.
    + destruct (IHp j eq_refl) as (H1 & H2).
      simpl. rewrite H1, H2. split; reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** The overflow target, in the [rep]-headed form the anchor glue states
    it in ([cden] produces [pre ++ rep u (a*j+b) ++ post]). *)
Lemma Gp_none_dst : forall j,
  S0 :: rep [S0] j ++ [S1; S1] = rep [S0] (S j) ++ [S1; S1].
Proof. reflexivity. Qed.
