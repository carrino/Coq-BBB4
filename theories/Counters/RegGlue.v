(** * RegGlue: the OCTAVE-PARITY view, for register x counter families.

    The "no overflow phase at K=6" bucket splits (WAVE28 section 3c) into
    families whose anchor FRAME -- the state and the constant cells on the
    far side of the head -- is not constant but depends on the octave the
    counter is in.  `tools/counters/regscan.py` chases the family forward and
    reads the frame off the machine; on the `period-2` rows the frame depends
    only on the PARITY of the octave, i.e. on the parity of
    [Pos.size_nat p - 1].

    That parity is what this file supplies, as a structural [Fixpoint] on
    [positive] together with the three facts a piecewise-[Cc] board needs:

    - [podd_succ_int]: an INTERIOR increment stays in its octave, so the
      frame does not move under it;
    - [podd_succ_fill]: an OVERFLOW increment crosses into the next octave,
      so the frame flips;
    - [podd_succ_pexp]: [2^k] and [2^k + 1] are in the SAME octave -- which
      is why a virtual anchor at a power of two and the ordinary anchor just
      above it carry the same frame.

    Everything else the register boards need already exists:
    [Counters/SkipGlue.v] fences the virtual anchors ([reach_ovf_skip],
    [vis_via_skip]), [Counters/NestedLapLift.v] carries the exponential
    branch ([nested_overflow_lift], [vis_via_fill]), and
    [Counters/LapGlue.v] closes an arbitrary [Cc].  This file adds no axiom
    and is closed under the global context. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter SkipGlue.
Import ListNotations.

(** The parity of the octave [p] lives in: [podd p = true] iff
    [Pos.size_nat p] is EVEN, i.e. iff [floor (log2 p)] is odd. *)
Fixpoint podd (p : positive) : bool :=
  match p with
  | xH => false
  | xO q => negb (podd q)
  | xI q => negb (podd q)
  end.

Lemma podd_bits : forall q, podd (xO q) = podd (xI q).
Proof. reflexivity. Qed.

(** An interior increment never leaves the octave. *)
Lemma podd_succ_int : forall p j q0, cview p = (j, Some q0) ->
  podd (Pos.succ p) = podd p.
Proof.
  induction p as [p IH|p IH|]; intros j q0 H; cbn in H.
  - destruct (cview p) as [j' oq] eqn:E.
    destruct oq as [r|]; [|discriminate].
    cbn [Pos.succ podd]. rewrite (IH j' r eq_refl). reflexivity.
  - reflexivity.
  - discriminate.
Qed.

(** An overflow increment crosses into the next octave, so the frame flips. *)
Lemma podd_succ_fill : forall p j, cview p = (S j, None) ->
  podd (Pos.succ p) = negb (podd p).
Proof.
  induction p as [p IH|p IH|]; intros j H; cbn in H.
  - destruct (cview p) as [j' oq] eqn:E.
    inversion H; subst j' oq; clear H.
    destruct j as [|j''].
    + exfalso. destruct p as [r|r|]; cbn in E;
        [destruct (cview r); discriminate | discriminate | discriminate].
    + cbn [Pos.succ podd]. rewrite (IH j'' eq_refl). reflexivity.
  - destruct (cview p) as [j' oq]; discriminate.
  - reflexivity.
Qed.

(** [2^(S k)] and [2^(S k) + 1] sit in the SAME octave. *)
Lemma podd_succ_pexp : forall p k, pexp p = Some (S k) ->
  podd (Pos.succ p) = podd p.
Proof.
  intros p k H. destruct (pexp_shape p k H) as (r & -> & _). reflexivity.
Qed.
