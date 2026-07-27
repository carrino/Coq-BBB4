(** * BCtrCounter: the BOUNCER-COUNTER closer.

    A bouncer counter (mxdys' reading; see
    docs/BOUNCER_COUNTER_READING.md for the sync variant) keeps two
    coupled quantities on the tape:

      qz(0) 1 0^(3*v + g0) 1 <binary counter of value v, low digit first>

    a BOUNCER whose length is affine in the counter's VALUE, and the
    counter itself beyond it, low digit adjacent to the bouncer.  Each
    digit is two cells: [S0;S0] = 0 and [S0;S1] = 1.

    That coupling is exactly what LapDecider cannot state (its symbolic
    side is indexed by the CARRY index j, not by the counter value p --
    docs/BOUNCER_COUNTER_READING.md, "Why LapDecider cannot see it").
    A hand proof does not need the two indices to interact, though:
    the bouncer sweep is uniform in whatever tail follows it, and the
    counter walk is uniform in whatever prefix precedes it.  So the
    lap factors into

      zipper (3 steps per gap cell, tail-uniform)
      entry  (3 steps across the two markers)
      walk   (2 steps per digit; a BLANK pair past the top digit is
              a digit-0 pair, so overflow and interior carry are the
              SAME rule -- this is what makes a bouncer counter
              simpler than a SYNC bouncer counter)
      sweep  (state qd walks back left blanking the bouncer)
      return (2 fresh blanks laid ahead of the bouncer: the gap grows
              by exactly 3, which is [cval (incr w) = S (cval w)])

    and ONE bouncer sweep is already a complete lap

      S(v) -->+ S(v+1)   in   4*(3*v+g0) + 4*carry(w) + 15 steps.

    The section below takes the nine gadget steps as hypotheses (each
    is a [csteps ... = Some ...] reflexivity in the machine file) and
    derives the lap, the intermediate reach points needed for the
    visit obligations, and never-quasihalting via [LapGlue].

    Customers: theories/Machines/Counters/BCtr_11.v and BCtr_13.v
    (BBB [blockdbl_counter] certificates #11 and #13, two of the 11
    live (4,2) holdouts).  This file is axiom-free. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue.
Import ListNotations.

(** ** List helpers *)

Lemma rep_snoc : forall (x : Sym) n l,
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma rep_split : forall (x : Sym) n m l,
  repeat x (n + m) ++ l = repeat x n ++ repeat x m ++ l.
Proof.
  induction n; intros m l; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

(** ** The counter word

    LOW digit first; digit [b] is the two cells [S0; b].  Words need no
    canonical form: leading zeros and the empty word are all fine, and
    nothing below inspects the top digit. *)

Fixpoint enc (w : list bool) : list Sym :=
  match w with
  | [] => []
  | b :: t => S0 :: (if b then S1 else S0) :: enc t
  end.

Fixpoint cval (w : list bool) : nat :=
  match w with
  | [] => 0
  | b :: t => (if b then 1 else 0) + 2 * cval t
  end.

(** The carry length: how many digit-1s the increment must clear. *)
Fixpoint carry (w : list bool) : nat :=
  match w with
  | true :: t => S (carry t)
  | _ => 0
  end.

(** What is left above the digit the increment sets. *)
Fixpoint crest (w : list bool) : list bool :=
  match w with
  | true :: t => crest t
  | false :: t => t
  | [] => []
  end.

Fixpoint incr (w : list bool) : list bool :=
  match w with
  | [] => [true]
  | false :: t => true :: t
  | true :: t => false :: incr t
  end.

Lemma cval_incr : forall w, cval (incr w) = S (cval w).
Proof.
  induction w as [|b t IH]; simpl; [reflexivity|].
  destruct b; simpl; [rewrite IH|]; lia.
Qed.

Lemma enc_incr : forall w,
  enc (incr w) = repeat S0 (2 * carry w) ++ S0 :: S1 :: enc (crest w).
Proof.
  induction w as [|b t IH]; simpl; [reflexivity|].
  destruct b; simpl; [|reflexivity].
  rewrite IH.
  replace (carry t + S (carry t + 0)) with (S (carry t + (carry t + 0))) by lia.
  reflexivity.
Qed.

(** [Pos.succ] on a positive IS the binary increment on its digit
    word, so a [LapGlue] chain indexed by [positive] is the counter
    counting. *)
Fixpoint bits (p : positive) : list bool :=
  match p with
  | xH => [true]
  | xO q => false :: bits q
  | xI q => true :: bits q
  end.

Lemma bits_succ : forall p, bits (Pos.succ p) = incr (bits p).
Proof.
  induction p as [p IH|p IH|]; simpl; try reflexivity.
  rewrite IH; reflexivity.
Qed.

(** ** The closer *)

Section BCtr.

Variable tm : TM.

(** [qz] anchors the family and runs the bouncer zipper; [qw] walks the
    counter digits; [qs] is where a digit-0 pair turns the walk around;
    [qd] sweeps back left.  [g0] is the gap offset, i.e. the bouncer's
    length at counter value 0. *)
Variable qz qw qs qd : St.
Variable g0 : nat.

(** Three steps eat one blank of the gap and lay one cell of the
    bouncer.  [Y] is arbitrary: this is what decouples the sweep from
    the counter. *)
Hypothesis Hzip : forall L Y,
  csteps tm 3 (qz, (L, S0, S1 :: S0 :: Y)) = Some (qz, (S1 :: L, S0, S1 :: Y)).

(** The head crosses the two markers and arrives at the low digit. *)
Hypothesis Hentry : forall L Y,
  csteps tm 3 (qz, (L, S0, S1 :: S1 :: Y))
  = Some (qw, (S1 :: S0 :: S1 :: L, chd Y, ctl Y)).

(** A digit-1 pair: both cells become ones, the walk carries on. *)
Hypothesis Hwalk1 : forall L Y,
  csteps tm 2 (qw, (L, S0, S1 :: Y)) = Some (qw, (S1 :: S1 :: L, chd Y, ctl Y)).

(** A digit-0 pair -- real, or a pair of blanks past the top digit:
    both cells become ones and the head turns around. *)
Hypothesis Hwalk0 : forall L Y,
  csteps tm 2 (qw, (L, S0, S0 :: Y)) = Some (qs, (L, S1, S1 :: Y)).

(** The same rule at the blank pair past the top digit.  On the tape
    this IS [Hwalk0] -- only [CTape]'s list representation tells the
    two apart, since a trailing blank is implicit rather than a cell.
    That the machine needs no separate OVERFLOW rule here is exactly
    what makes a bouncer counter cheaper than a sync bouncer counter. *)
Hypothesis Hwalk0e : forall L,
  csteps tm 2 (qw, (L, S0, [])) = Some (qs, (L, S1, [S1])).

Hypothesis Hturn : forall L R,
  csteps tm 1 (qs, (S1 :: L, S1, R)) = Some (qd, (L, S1, S0 :: R)).

Hypothesis Hd11 : forall L R,
  csteps tm 1 (qd, (S1 :: L, S1, R)) = Some (qd, (L, S1, S0 :: R)).

Hypothesis Hd10 : forall L R,
  csteps tm 1 (qd, (S0 :: L, S1, R)) = Some (qd, (L, S0, S0 :: R)).

(** The turnaround at the separator, launching the long return. *)
Hypothesis Hret5 : forall M E,
  csteps tm 5 (qd, (S1 :: M, S0, S0 :: E)) = Some (qd, (M, S1, S0 :: S1 :: E)).

(** Off the left end: two blanks are laid ahead of the bouncer, and the
    next anchor's head cell is reached. *)
Hypothesis Hret3 : forall R,
  csteps tm 3 (qd, ([], S1, R)) = Some (qz, ([], S0, S1 :: S0 :: S0 :: R)).

(** *** Derived runs *)

Lemma zipn : forall j L Y,
  csteps tm (3 * j) (qz, (L, S0, S1 :: repeat S0 j ++ Y))
  = Some (qz, (repeat S1 j ++ L, S0, S1 :: Y)).
Proof.
  induction j as [|j IH]; intros L Y.
  - reflexivity.
  - replace (3 * S j) with (3 + 3 * j) by lia.
    rewrite csteps_add.
    change (repeat S0 (S j) ++ Y) with (S0 :: (repeat S0 j ++ Y)).
    rewrite Hzip, IH.
    change (repeat S1 (S j) ++ L) with (S1 :: (repeat S1 j ++ L)).
    rewrite rep_snoc. reflexivity.
Qed.

(** The rightward digit walk.  ONE induction covers the interior carry
    and the overflow: [enc [] = []], and [chd []]/[ctl []] hand the
    walk a blank pair, which is exactly a digit-0 pair. *)
Lemma run_fwd : forall w L,
  csteps tm (2 * carry w + 2) (qw, (L, chd (enc w), ctl (enc w)))
  = Some (qs, (repeat S1 (2 * carry w) ++ L, S1, S1 :: enc (crest w))).
Proof.
  induction w as [|b t IH]; intros L.
  - apply Hwalk0e.
  - destruct b.
    + change (enc (true :: t)) with (S0 :: S1 :: enc t).
      change (chd (S0 :: S1 :: enc t)) with S0.
      change (ctl (S0 :: S1 :: enc t)) with (S1 :: enc t).
      change (carry (true :: t)) with (S (carry t)).
      change (crest (true :: t)) with (crest t).
      replace (2 * S (carry t) + 2) with (2 + (2 * carry t + 2)) by lia.
      rewrite csteps_add, Hwalk1, IH.
      replace (2 * S (carry t)) with (2 * carry t + 2) by lia.
      rewrite rep_split. reflexivity.
    + change (enc (false :: t)) with (S0 :: S0 :: enc t).
      change (chd (S0 :: S0 :: enc t)) with S0.
      change (ctl (S0 :: S0 :: enc t)) with (S0 :: enc t).
      change (carry (false :: t)) with 0.
      change (crest (false :: t)) with t.
      rewrite Hwalk0. reflexivity.
Qed.

(** [qd] walks left over a run of ones, blanking it. *)
Lemma dsw : forall k L R,
  csteps tm k (qd, (repeat S1 k ++ L, S1, R))
  = Some (qd, (L, S1, repeat S0 k ++ R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S1 (1 + k) ++ L) with (S1 :: (repeat S1 k ++ L)).
    rewrite csteps_add, Hd11, IH.
    change (repeat S0 (1 + k) ++ R) with (S0 :: (repeat S0 k ++ R)).
    rewrite rep_snoc. reflexivity.
Qed.

(** The whole increment: walk the trailing 1-digits, set the first
    0-digit (real or virtual), sweep back to the separator.  The
    counter word comes out as [incr w] on the nose. *)
Lemma ctr : forall w M,
  csteps tm (4 * carry w + 4) (qw, (S1 :: S0 :: M, chd (enc w), ctl (enc w)))
  = Some (qd, (M, S0, S0 :: enc (incr w))).
Proof.
  intros w M.
  replace (4 * carry w + 4)
     with ((2 * carry w + 2) + (1 + (2 * carry w + 1))) by lia.
  rewrite csteps_add, run_fwd, rep_snoc, csteps_add, Hturn, csteps_add, dsw,
          Hd10, enc_incr.
  reflexivity.
Qed.

(** Out of the separator, past the bouncer, to the new leftmost cell.
    The bouncer's [G] ones are blanked and two extra blanks are laid
    ahead of it, so the gap grows by exactly 3. *)
Lemma ret : forall G E,
  csteps tm (G + 8) (qd, (repeat S1 (S G), S0, S0 :: E))
  = Some (qz, ([], S0, S1 :: repeat S0 (G + 3) ++ S1 :: E)).
Proof.
  intros G E.
  replace (G + 8) with (5 + (G + 3)) by lia.
  change (repeat S1 (S G)) with (S1 :: repeat S1 G).
  rewrite csteps_add, Hret5.
  replace (repeat S1 G) with (repeat S1 G ++ @nil Sym)
    by (rewrite app_nil_r; reflexivity).
  rewrite csteps_add, dsw, Hret3.
  replace (G + 3) with (3 + G) by lia.
  rewrite rep_split.
  change (repeat S0 3) with [S0; S0; S0].
  simpl (([S0; S0; S0] ++ repeat S0 G ++ S1 :: E)).
  rewrite rep_snoc. reflexivity.
Qed.

(** *** The anchor family and the lap *)

Definition gap (w : list bool) : nat := 3 * cval w + g0.

Definition anchor (w : list bool) : cconf :=
  (qz, ([], S0, S1 :: repeat S0 (gap w) ++ S1 :: enc w)).

Lemma gap_incr : forall w, gap (incr w) = gap w + 3.
Proof. intros w; unfold gap; rewrite cval_incr; lia. Qed.

(** End of the zipper: the gap has become the bouncer. *)
Lemma zip_end : forall w,
  csteps tm (3 * gap w) (anchor w)
  = Some (qz, (repeat S1 (gap w), S0, S1 :: S1 :: enc w)).
Proof.
  intros w. unfold anchor. rewrite zipn, app_nil_r. reflexivity.
Qed.

(** End of the counter phase: the head is back on the separator. *)
Lemma ctr_end : forall w,
  csteps tm (3 * gap w + (3 + (4 * carry w + 4))) (anchor w)
  = Some (qd, (repeat S1 (S (gap w)), S0, S0 :: enc (incr w))).
Proof.
  intros w.
  rewrite csteps_add, zip_end, csteps_add, Hentry.
  change (S1 :: S0 :: S1 :: repeat S1 (gap w))
    with (S1 :: S0 :: repeat S1 (S (gap w))).
  apply ctr.
Qed.

(** One bouncer sweep: S(v) -->+ S(v+1). *)
Lemma bc_lap : forall w,
  csteps tm (4 * gap w + 4 * carry w + 15) (anchor w) = Some (anchor (incr w)).
Proof.
  intros w.
  replace (4 * gap w + 4 * carry w + 15)
     with ((3 * gap w + (3 + (4 * carry w + 4))) + (gap w + 8))
     by (unfold gap; lia).
  rewrite csteps_add, ctr_end, ret.
  unfold anchor. rewrite gap_incr. reflexivity.
Qed.

Definition Cc (p : positive) : cconf := anchor (bits p).

(** Never-quasihalting, given a bootstrap and the four visit
    witnesses.  [Cc] chains forever because [Pos.succ] is [incr]. *)
Theorem bc_neverqh :
  (exists t0, stepn tm t0 InitES = Some (lift (Cc 1))) ->
  (forall w q, exists k c, csteps tm k (anchor w) = Some c /\ fst c = q) ->
  NeverQuasiHaltsSt tm.
Proof.
  intros Hboot Hvis.
  apply (glue_neverqh tm Cc 1).
  - exact Hboot.
  - intros p _. unfold Cc. rewrite bits_succ.
    exists (4 * gap (bits p) + 4 * carry (bits p) + 15), (anchor (incr (bits p))).
    split; [apply bc_lap | split; [reflexivity | unfold gap; lia]].
  - intros p q _. apply Hvis.
Qed.

End BCtr.
