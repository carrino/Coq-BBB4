(** * Sep2Counter: the SEPARATOR-2 bouncer counter closer.

    A second bouncer-counter shape, adjacent to [BCtrCounter] but with
    the roles of the two sides exchanged and a two-cell separator.  The
    anchor is

      (qd) 0 1 1 [1] 1 0^(2*v + 2) 1 1 <binary counter of value v, low
                                        digit first, ONE cell per digit>

    -- a fixed three-cell WALL on the left, the head on a marker, then a
    zipper gap whose length is affine in the counter's value, the two
    separator cells, and the counter beyond them.  The wall never moves
    relative to the head, so the whole family is one [cconf] with a
    constant left list; on the two-way tape the picture is a wall
    marching left at two cells per lap while the counter creeps right.

    The lap factors the same way a bouncer counter always does -- the
    zipper is uniform in whatever tail follows it, the digit walk is
    uniform in whatever prefix precedes it:

      prelude  (2 steps across the wall marker)
      zipper   (5 steps per gap cell, tail-uniform: the gap becomes a
                run of ones)
      entry    (4 steps across the marker and the two separator cells)
      walk     (1 step per digit-1; the first digit-0 -- real, or the
                BLANK past the top digit, which is the same rule -- is
                set and the head turns)
      sweep    ([qc] walks back left blanking the ones it meets, 1 step
                per cell, stopping at the [S0] the entry left behind)
      turn     (8 steps rebuilding the two separator cells)
      sweep    (again, this time off the left end of the tape)
      tail     (14 steps laying the new wall and marker; the gap grows
                by exactly 2, which is [cval (incr w) = S (cval w)])

    and one sweep is a complete lap

      S(v) -->+ S(v+1)   in   6*(2*v+2) + 2*carry(w) + 36 steps.

    As in [BCtrCounter] the overflow needs no separate rule: [enc1 [] =
    []], and [chd []]/[ctl []] hand the walk a blank, which is exactly a
    digit-0.

    Customers: theories/Machines/Counters/Sep2_0RB0RD_1LC1RB_1RA0LC_1LB0LC.v
    and Sep2_..._1LD0LC.v -- the two [SEP2_EARLY_ONLY] rows of the core
    (tools/counter_encodings.tsv).  Those two machines differ only in
    [D 0] ([1LB] vs [1LD]), and the difference is invisible here: both
    detours have the same length and the same tape effect, so the two
    machines have literally the same orbit and discharge the same
    gadget list.  This file is axiom-free. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue BCtrCounter.
Import ListNotations.

(** ** The counter word, one cell per digit

    [cval], [carry], [crest], [incr], [bits] and their algebra are
    [BCtrCounter]'s; only the tape encoding differs (one cell here,
    two there). *)

Fixpoint enc1 (w : list bool) : list Sym :=
  match w with
  | [] => []
  | b :: t => (if b then S1 else S0) :: enc1 t
  end.

Lemma enc1_incr : forall w,
  enc1 (incr w) = repeat S0 (carry w) ++ S1 :: enc1 (crest w).
Proof.
  induction w as [|b t IH]; simpl; [reflexivity|].
  destruct b; simpl; [rewrite IH|]; reflexivity.
Qed.

Section Sep2.

Variable tm : TM.

(** [qd] anchors the family (head on the wall marker); [qa] runs the
    zipper; [qb] walks the counter digits; [qc] sweeps back left. *)
Variable qa qb qc qd : St.

(** The prelude: two steps turn the wall's [S0] into a [S1] and hand
    the zipper its start. *)
Hypothesis Hpre : forall L R,
  csteps tm 2 (qd, (S0 :: L, S1, R)) = Some (qa, (S1 :: L, S0, R)).

(** Five steps eat one blank of the gap and lay one cell of ones.
    [Y] is arbitrary: this is what decouples the zipper from the
    counter. *)
Hypothesis Hzip : forall L Y,
  csteps tm 5 (qa, (L, S0, S1 :: S0 :: Y))
  = Some (qa, (S1 :: L, S0, S1 :: Y)).

(** The head crosses the marker and the two separator cells and
    arrives at the low digit. *)
Hypothesis Hentry : forall L Y,
  csteps tm 4 (qa, (L, S0, S1 :: S1 :: S1 :: Y))
  = Some (qb, (S1 :: S1 :: S1 :: S0 :: L, chd Y, ctl Y)).

(** A digit-1: the walk carries on. *)
Hypothesis Hone : forall L Y,
  csteps tm 1 (qb, (L, S1, Y)) = Some (qb, (S1 :: L, chd Y, ctl Y)).

(** A digit-0 -- real, or the blank past the top digit: it is set and
    the head turns around. *)
Hypothesis Hzero : forall L Y,
  csteps tm 1 (qb, (L, S0, Y)) = Some (qc, (ctl L, chd L, S1 :: Y)).

(** [qc] blanks one cell and steps left.  Stated with [chd]/[ctl] so
    that it also fires off the left end of the tape. *)
Hypothesis Hclr : forall L R,
  csteps tm 1 (qc, (L, S1, R)) = Some (qc, (ctl L, chd L, S0 :: R)).

(** The turnaround: the two separator cells are rebuilt. *)
Hypothesis Hturn : forall L R,
  csteps tm 8 (qc, (L, S0, S0 :: S0 :: S0 :: R))
  = Some (qc, (L, S1, S0 :: S1 :: S1 :: R)).

(** Off the left end: the new wall and marker are laid, and the next
    anchor's head cell is reached. *)
Hypothesis Htail : forall R,
  csteps tm 14 (qc, ([], S0, S0 :: S0 :: S0 :: R))
  = Some (qd, ([S0; S1; S1], S1, S1 :: R)).

(** *** Derived runs *)

Lemma zipn : forall j L Y,
  csteps tm (5 * j) (qa, (L, S0, S1 :: repeat S0 j ++ Y))
  = Some (qa, (repeat S1 j ++ L, S0, S1 :: Y)).
Proof.
  induction j as [|j IH]; intros L Y.
  - reflexivity.
  - replace (5 * S j) with (5 + 5 * j) by lia.
    rewrite csteps_add.
    change (repeat S0 (S j) ++ Y) with (S0 :: (repeat S0 j ++ Y)).
    rewrite Hzip, IH.
    change (repeat S1 (S j) ++ L) with (S1 :: (repeat S1 j ++ L)).
    rewrite rep_snoc. reflexivity.
Qed.

(** The digit walk.  ONE induction covers the interior carry and the
    overflow: [enc1 [] = []], and [chd []]/[ctl []] hand the walk a
    blank, which is exactly a digit-0. *)
Lemma run_walk : forall w L,
  csteps tm (carry w + 1) (qb, (L, chd (enc1 w), ctl (enc1 w)))
  = Some (qc, (ctl (repeat S1 (carry w) ++ L),
               chd (repeat S1 (carry w) ++ L),
               S1 :: enc1 (crest w))).
Proof.
  induction w as [|b t IH]; intros L.
  - apply Hzero.
  - destruct b.
    + change (enc1 (true :: t)) with (S1 :: enc1 t).
      change (chd (S1 :: enc1 t)) with S1.
      change (ctl (S1 :: enc1 t)) with (enc1 t).
      change (carry (true :: t)) with (S (carry t)).
      change (crest (true :: t)) with (crest t).
      replace (S (carry t) + 1) with (1 + (carry t + 1)) by lia.
      rewrite csteps_add, Hone, IH.
      change (repeat S1 (S (carry t)) ++ L) with (S1 :: (repeat S1 (carry t) ++ L)).
      rewrite rep_snoc. reflexivity.
    + change (enc1 (false :: t)) with (S0 :: enc1 t).
      change (chd (S0 :: enc1 t)) with S0.
      change (ctl (S0 :: enc1 t)) with (enc1 t).
      apply Hzero.
Qed.

(** [qc] walks left over a run of ones, blanking it. *)
Lemma csw : forall k L R,
  csteps tm k (qc, (repeat S1 k ++ L, S1, R))
  = Some (qc, (L, S1, repeat S0 k ++ R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S1 (1 + k) ++ L) with (S1 :: (repeat S1 k ++ L)).
    rewrite csteps_add, Hclr.
    change (ctl (S1 :: (repeat S1 k ++ L))) with (repeat S1 k ++ L).
    change (chd (S1 :: (repeat S1 k ++ L))) with S1.
    rewrite IH.
    change (repeat S0 (1 + k) ++ R) with (S0 :: (repeat S0 k ++ R)).
    rewrite rep_snoc. reflexivity.
Qed.

(** *** The anchor family and the lap *)

Definition gap (w : list bool) : nat := 2 * cval w + 2.

Definition anchor (w : list bool) : cconf :=
  (qd, ([S0; S1; S1], S1,
        S1 :: repeat S0 (gap w) ++ S1 :: S1 :: enc1 w)).

Lemma gap_incr : forall w, gap (incr w) = gap w + 2.
Proof. intros w; unfold gap; rewrite cval_incr; lia. Qed.

(** End of the zipper: the gap has become a run of ones. *)
Lemma zip_end : forall w,
  csteps tm (2 + 5 * gap w) (anchor w)
  = Some (qa, (repeat S1 (gap w + 3), S0, S1 :: S1 :: S1 :: enc1 w)).
Proof.
  intros w. unfold anchor.
  rewrite csteps_add, Hpre, zipn.
  change (S1 :: [S1; S1]) with (repeat S1 3).
  rewrite <- repeat_app. reflexivity.
Qed.

(** End of the counter phase: the head is back on the [S0] the entry
    left behind, and the counter reads [incr w]. *)
Lemma ctr_end : forall w,
  csteps tm (2 + 5 * gap w + (4 + (carry w + 1)) + (carry w + 2 + 1)) (anchor w)
  = Some (qc, (repeat S1 (gap w + 3), S0, S0 :: S0 :: S0 :: enc1 (incr w))).
Proof.
  intros w.
  assert (HM : repeat S1 (carry w) ++ S1 :: S1 :: S1 :: S0 :: repeat S1 (gap w + 3)
             = S1 :: (repeat S1 (carry w + 2) ++ S0 :: repeat S1 (gap w + 3))).
  { change (S1 :: S1 :: S1 :: S0 :: repeat S1 (gap w + 3))
      with (repeat S1 3 ++ S0 :: repeat S1 (gap w + 3)).
    rewrite <- rep_split.
    replace (carry w + 3) with (S (carry w + 2)) by lia.
    reflexivity. }
  assert (HR : S0 :: repeat S0 (carry w + 2) ++ S1 :: enc1 (crest w)
             = S0 :: S0 :: S0 :: enc1 (incr w)).
  { rewrite enc1_incr.
    change (S0 :: repeat S0 (carry w + 2) ++ S1 :: enc1 (crest w))
      with (repeat S0 (1 + (carry w + 2)) ++ S1 :: enc1 (crest w)).
    change (S0 :: S0 :: S0 :: (repeat S0 (carry w) ++ S1 :: enc1 (crest w)))
      with (repeat S0 3 ++ repeat S0 (carry w) ++ S1 :: enc1 (crest w)).
    rewrite <- rep_split.
    replace (1 + (carry w + 2)) with (3 + carry w) by lia.
    reflexivity. }
  rewrite csteps_add, csteps_add, zip_end, csteps_add, Hentry, run_walk, HM.
  cbn [chd ctl].
  rewrite csteps_add, csw, Hclr.
  cbn [chd ctl].
  rewrite HR. reflexivity.
Qed.

(** One bouncer sweep: S(v) -->+ S(v+1). *)
Lemma s2_lap : forall w,
  csteps tm (6 * gap w + 2 * carry w + 36) (anchor w) = Some (anchor (incr w)).
Proof.
  intros w.
  assert (HT : S0 :: repeat S0 (gap w + 3) ++ S0 :: S1 :: S1 :: enc1 (incr w)
             = S0 :: S0 :: S0 :: (repeat S0 (gap w + 2) ++ S1 :: S1 :: enc1 (incr w))).
  { replace (gap w + 3) with (2 + (gap w + 1)) by lia.
    replace (gap w + 2) with (S (gap w + 1)) by lia.
    cbn [repeat]. rewrite rep_snoc. reflexivity. }
  replace (6 * gap w + 2 * carry w + 36)
     with ((2 + 5 * gap w + (4 + (carry w + 1)) + (carry w + 2 + 1))
           + (8 + ((gap w + 3) + (1 + 14)))) by lia.
  rewrite csteps_add, ctr_end, csteps_add, Hturn, csteps_add.
  replace (repeat S1 (gap w + 3)) with (repeat S1 (gap w + 3) ++ @nil Sym)
    by (rewrite app_nil_r; reflexivity).
  rewrite csw, csteps_add, Hclr.
  cbn [chd ctl].
  rewrite HT, Htail.
  unfold anchor. rewrite gap_incr. reflexivity.
Qed.

Definition Cc (p : positive) : cconf := anchor (bits p).

(** Never-quasihalting, given a bootstrap and the visit witnesses.
    [Cc] chains forever because [Pos.succ] is [incr]. *)
Theorem s2_neverqh :
  (exists t0, stepn tm t0 InitES = Some (lift (Cc 1))) ->
  (forall q Y, exists k c,
      csteps tm k (qd, ([S0; S1; S1], S1, S1 :: S0 :: Y)) = Some c /\ fst c = q) ->
  NeverQuasiHaltsSt tm.
Proof.
  intros Hboot Hvis.
  apply (glue_neverqh tm Cc 1).
  - exact Hboot.
  - intros p _. unfold Cc. rewrite bits_succ.
    exists (6 * gap (bits p) + 2 * carry (bits p) + 36), (anchor (incr (bits p))).
    split; [apply s2_lap | split; [reflexivity | unfold gap; lia]].
  - intros p q _. unfold Cc, anchor.
    replace (gap (bits p)) with (2 + 2 * cval (bits p)) by (unfold gap; lia).
    cbn [repeat].
    apply Hvis.
Qed.

End Sep2.
