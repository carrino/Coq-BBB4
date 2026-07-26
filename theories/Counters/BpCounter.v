(** * BpCounter: the BLANK-SEPARATED counter encoding.

    The seventh counter word family.  [ILCounter.Ip] and [JpCounter.Jp] put
    an [S1] marker BEFORE each bit, [MpCounter.Mp] puts one AFTER,
    [DpCounter.Dp] doubles each bit, [KpCounter.Kp] has no separator at all,
    and [GpCounter.Gp] is the Gray code.  This one separates the bits with a
    BLANK:

      Bp p = S0 b0 S0 b1 ... S0 bk      (LSB nearest the head, MSB deepest)

    Every previously known alphabet separates with [S1] or not at all, which
    is exactly why the anchor search reported "no anchor family" on this
    population: a blank separator makes the word look like sparse noise to a
    recognizer built for [S1] combs.

    Human read of [1RB0RB_1LC1RA_1RA0LD_0LB0LD]: "a counter on the right and
    big triangles out that grow in size by 1 for each pass".  The counter is
    the word below; the triangles are a separate matter (see
    WAVE14_FINDINGS.md -- that machine's far side GROWS, so it has no fixed
    anchor even with the right alphabet).  Measured over the no-anchor
    bucket, 26% of a 120-machine sample decodes under this word with a long
    consecutive run, most of them with a FIXED far side.

    On the tape the word is usually preceded by a single [S1] at the head end
    ([S1 :: Bp p]); that cell is part of the anchor's surroundings, not of the
    encoding, so [Bp] itself is what the lap templates consume.

    Axiom footprint: none (closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

Fixpoint Bp (p : positive) : list Sym :=
  match p with
  | xH => [S0; S1]
  | xO q => S0 :: S0 :: Bp q
  | xI q => S0 :: S1 :: Bp q
  end.

Lemma Bp_nonnil : forall p, exists w, Bp p = S0 :: w.
Proof. destruct p; simpl; eauto. Qed.

(** ** The two decomposition lemmas the lap templates consume *)

(** Interior increment: [j] trailing set bits clear, the first clear bit
    sets.  The blank separators are untouched. *)
Lemma cview_some_B : forall p j q, cview p = (j, Some q) ->
  Bp p = rep [S0; S1] j ++ S0 :: S0 :: Bp q /\
  Bp (Pos.succ p) = rep [S0; S0] j ++ S0 :: S1 :: Bp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl; [rewrite H1 | rewrite H2]; reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

(** Overflow: the all-ones word becomes all-clear plus a fresh top bit, each
    still carrying its blank separator. *)
Lemma cview_none_B : forall p j, cview p = (S j, None) ->
  Bp p = rep [S0; S1] (S j) /\
  Bp (Pos.succ p) = rep [S0; S0] (S j) ++ [S0; S1].
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
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** The pair rotation the interior junction needs, as in [JpCounter.pair_rot]
    and [MpCounter.pair_rot_M]. *)
Lemma pair_rot_B : forall (x y : Sym) j, rep [x; y] j ++ [x] = x :: rep [y; x] j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.
