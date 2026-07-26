(** * MpCounter: the MARKER-AFTER interleaved counter encoding.

    The fifth counter encoding, alongside [ILCounter.Ip] and
    [JpCounter.Jp] (marker BEFORE each bit), [KpCounter.Kp] (no marker at
    all) and [DpCounter.Dp] (each bit doubled).  Here every bit is followed
    by its marker cell:

      Mp p = b0 S1 b1 S1 ... bk S1     (LSB nearest the head, MSB deepest)

    Human read of [0RB---_0RC0LD_1LD1RC_0LA1LB]: "a counter, msb on the
    right, 1 to the right of every bit".  Read nearest-first from a head at
    the LEFT end of a right-growing counter -- or, after mirroring, from the
    right end of a left-growing one -- that is exactly the word below.

    The distinction from [Ip] is a ONE-CELL FRAME SHIFT, which is why the
    Ip recognizers half-fire on this family: when b0 = 1 the word opens
    [S1;S1] just as an Ip word does, so a prefix decodes and the lap
    templates then miss.  Measured over the wave-12 residue, ~1 machine in 5
    carries this encoding.

    Unlike the width-widening family (docs/UNCERTAIN_MACHINES.md section 1)
    this counter visits EVERY value -- measured 1..1023 consecutively on the
    exemplar -- so [Pos.succ] is the right successor and [LapGlue] applies
    unchanged.

    Axiom footprint: none (closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

Fixpoint Mp (p : positive) : list Sym :=
  match p with
  | xH => [S1; S1]
  | xO q => S0 :: S1 :: Mp q
  | xI q => S1 :: S1 :: Mp q
  end.

Lemma Mp_nonnil : forall p, exists w, Mp p = w ++ [S1] /\ w <> [].
Proof.
  induction p as [p IH | p IH |].
  - destruct IH as (w & Hw & Hne). exists (S1 :: S1 :: w).
    split; [simpl; rewrite Hw; reflexivity | discriminate].
  - destruct IH as (w & Hw & Hne). exists (S0 :: S1 :: w).
    split; [simpl; rewrite Hw; reflexivity | discriminate].
  - exists [S1]. split; reflexivity || discriminate.
Qed.

(** The marker cell is always the second cell of the word. *)
Lemma Mp_shape : forall p, exists b w, Mp p = b :: S1 :: w.
Proof. destruct p; simpl; eauto. Qed.

(** ** The two decomposition lemmas the lap templates consume *)

(** Interior increment: [j] trailing set bits flip to clear, the first
    clear bit sets.  The markers are untouched. *)
Lemma cview_some_M : forall p j q, cview p = (j, Some q) ->
  Mp p = rep [S1; S1] j ++ S0 :: S1 :: Mp q /\
  Mp (Pos.succ p) = rep [S0; S1] j ++ S1 :: S1 :: Mp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl; [rewrite H1 | rewrite H2]; reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

(** Overflow: the all-ones word becomes all-clear plus a fresh top bit,
    each with its marker. *)
Lemma cview_none_M : forall p j, cview p = (S j, None) ->
  Mp p = rep [S1; S1] (S j) /\
  Mp (Pos.succ p) = rep [S0; S1] (S j) ++ [S1; S1].
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

(** The pair rotation the interior junction needs, mirroring
    [JpCounter.pair_rot] but for the marker-after frame. *)
Lemma pair_rot_M : forall (x y : Sym) j, rep [x; y] j ++ [x] = x :: rep [y; x] j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.
