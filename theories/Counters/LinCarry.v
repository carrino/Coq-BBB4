(** * LinCarry: binary counters whose carry is done by LINEAR SEARCH.

    Three of the undecided core rows (tools/closeout/core_rows.txt) are
    plain base-2 counters under the [KpCounter.Kp] alphabet -- one cell
    per digit, LSB nearest the head, nothing between the bits -- whose
    INCREMENT is not a single sweep.  The carry run is cleared by a
    bouncer: the machine makes one round trip per digit of the run, so a
    lap over a carry of length [j] costs [Theta(j^2)] steps and no single
    LapDecider chain reaches it at any framing.  That is the shape
    WAVE26 section 7 named QUAD/QUAD, and [Counters/QuadGlue.v] is the
    same composition done through [MeasureGlue.mrun]; the rows here are
    the ones whose micro laps the chain language cannot spell
    (`quad_emit.py` refuses all three, `no TCp chain`), so their round
    trips are derived directly, by induction on the run length.

    Two shapes, one section each, and both laps are complete -- anchor to
    anchor, with no auxiliary index escaping into the family:

    - [Plain] (customer 1RB1LA_0LA1RC_0LD0RC_1LD0RB).  The anchor is the
      bare counter, head on the blank just past the low digit:

        anchor p :  <Kp p, low digit adjacent>  [qB:0]

      [qB] turns the head around, [qA] walks left over the carry run and
      SETS the stop digit, then the run is cleared right-to-left by
      [qC]/[qD] round trips, one per digit, each two steps shorter than
      the last.  Lap [(j+1)*(j+2)] steps.

    - [Spacer] (customers 1RB0LD_0LC0RB_1LA1RC_0RC1LD and, through
      [Mirror], 1RB1LA_1LC0RD_0RA0LC_0LA1RD).  One blank SPACER cell sits
      between the counter and the head:

        anchor p :  <Kp p, low digit adjacent>  0  [qB:0]

      so the tape word reads [2*v] and its low cell is never a digit.
      Here the hole runs the OTHER way -- [qA] opens it at the low digit
      and each [qD]/[qC] round trip drives it one cell deeper into the
      run, refilling behind itself -- and the finished run is blanked by
      a single [qB] sweep on the way out.  Lap [j^2+3*j+4] steps.

    In both sections the OVERFLOW lap needs no separate rule.  The
    anchor's word carries one padding blank ([Kp p ++ [S0]]), invisible
    to [lift]; that pad IS the stop digit when the counter is a solid run
    of ones, so [cview]'s two cases collapse to one lemma with the deep
    word [W] instantiated to [Kp q ++ [S0]] or to [[]].

    The machine is abstract here: each section takes the eight
    transitions it uses as already-applied [cstep] gadgets, so nothing
    below ever computes on an unknown table, and a customer discharges
    them by [reflexivity].  Every lap and step count was checked
    differentially against the raw simulator (exact [cconf], exact
    totals) for [j = 0..10] against seven deep words before any of it was
    written.  This file is axiom-free; the boards that import it carry
    [functional_extensionality_dep] through [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter KpCounter
                                  LapCertGlue.
Import ListNotations.

(** ** The padded carry view

    [cview] splits [p] into its low run of set bits and what is above
    them, and [KpCounter] reads that back off the tape -- but in two
    shapes, [rep [S1] j ++ S0 :: Kp q] for an interior carry and
    [rep [S1] (S j)] for an overflow.  Appending one blank cell merges
    them: the pad plays the stop digit at an overflow, with deep word
    [[]]. *)

Lemma Kp_pad_split : forall p, exists j W, Kp p ++ [S0] = rep [S1] j ++ S0 :: W.
Proof.
  intros p. destruct (cview p) as [j o] eqn:E. destruct o as [q|].
  - destruct (cview_some_K p j q E) as (H1 & _).
    exists j, (Kp q ++ [S0]). rewrite H1, <- app_assoc. reflexivity.
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (cview_none_K p j' E) as (H1 & _).
    exists (S j'), []. rewrite H1. reflexivity.
Qed.

(** The lap's two ends -- and, for the visit obligation, the fact that a
    lap out of an EVEN anchor lands on one whose carry run is non-empty:
    the deep word of a [j = 0] split is itself a word, so the [S1] the
    lap sets is followed by a genuine split. *)
Lemma Kp_lap_split : forall p, exists j W,
  Kp p ++ [S0] = rep [S1] j ++ S0 :: W /\
  (rep [S0] j ++ S1 :: W = Kp (Pos.succ p) ++ [S0] \/
   (rep [S0] j ++ S1 :: W) ++ [S0] = Kp (Pos.succ p) ++ [S0]) /\
  (j = 0 -> exists j2 W2, W = rep [S1] j2 ++ S0 :: W2).
Proof.
  intros p. destruct (cview p) as [j o] eqn:E. destruct o as [q|].
  - destruct (cview_some_K p j q E) as (H1 & H2).
    exists j, (Kp q ++ [S0]). split; [rewrite H1, <- app_assoc; reflexivity|].
    split.
    + left. rewrite H2, app_comm_cons, app_assoc. reflexivity.
    + intros _. apply Kp_pad_split.
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (cview_none_K p j' E) as (H1 & H2).
    exists (S j'), []. split; [rewrite H1; reflexivity|].
    split; [right; rewrite H2; reflexivity | discriminate].
Qed.

(** A trailing blank on either half-tape is invisible to [lift]: an
    overflow lap lands one written blank past the anchor's left end. *)
Lemma lift_pad_eq : forall q pre X Y,
  (X = Y \/ X ++ [S0] = Y) ->
  lift (q, (pre ++ X, S0, [])) = lift (q, (pre ++ Y, S0, [])).
Proof.
  intros q pre X Y [H|H]; subst; [reflexivity|].
  rewrite app_assoc. symmetry. apply lift_app_blank_l.
Qed.

(** [rep] of a one-cell block, at the head and at the tail. *)
Lemma rep1_cons : forall (x : Sym) k, rep [x] (S k) = x :: rep [x] k.
Proof. reflexivity. Qed.

Lemma rep1_snoc : forall (x : Sym) k l,
  rep [x] k ++ x :: l = rep [x] (S k) ++ l.
Proof.
  intros x k l. change (x :: l) with ([x] ++ l).
  rewrite app_assoc, rep_shift. reflexivity.
Qed.

(** A run laid on top of a non-empty tail is a non-empty list -- what the
    visit lemmas need to fire a gadget on it. *)
Lemma rep_cons_ne : forall (x : Sym) k y l,
  exists h t, rep [x] k ++ y :: l = h :: t.
Proof. intros x [|k] y l; simpl; eauto. Qed.

(** ** Composing runs

    [csteps_add] leaves a [match] that blocks the next [rewrite]; these
    two rewrite a prefix away outright. *)
Section Compose.
Variable tm : TM.

Lemma stepR : forall n c c',
  cstep tm c = Some c' -> csteps tm (S n) c = csteps tm n c'.
Proof. intros n c c' H. cbn [csteps]. rewrite H. reflexivity. Qed.

Lemma stepN : forall a b c c',
  csteps tm a c = Some c' -> csteps tm (a + b) c = csteps tm b c'.
Proof. intros a b c c' H. rewrite csteps_add, H. reflexivity. Qed.

End Compose.

(** * The PLAIN shape: no spacer, and the hole runs toward the head *)

Section Plain.

Variable tm : TM.
Variable qA qB qC qD : St.

Hypothesis Hcover : forall q : St, q = qA \/ q = qB \/ q = qC \/ q = qD.

(** [1RB] -- turn right, setting the stop digit. *)
Hypothesis PA0 : forall l h r,
  cstep tm (qA, (l, S0, h :: r)) = Some (qB, (S1 :: l, h, r)).
(** [1LA] -- walk left over the carry run. *)
Hypothesis PA1 : forall l h r,
  cstep tm (qA, (h :: l, S1, r)) = Some (qA, (l, h, S1 :: r)).
(** [0LA] -- the anchor's turnaround. *)
Hypothesis PB0 : forall l h r,
  cstep tm (qB, (h :: l, S0, r)) = Some (qA, (l, h, S0 :: r)).
(** [1RC] -- start a round trip. *)
Hypothesis PB1 : forall l h r,
  cstep tm (qB, (l, S1, h :: r)) = Some (qC, (S1 :: l, h, r)).
(** [0LD] -- the far turn of a round trip. *)
Hypothesis PC0 : forall l h r,
  cstep tm (qC, (h :: l, S0, r)) = Some (qD, (l, h, S0 :: r)).
(** [0RC] -- blank the run on the way out. *)
Hypothesis PC1 : forall l h r,
  cstep tm (qC, (l, S1, h :: r)) = Some (qC, (S0 :: l, h, r)).
(** [1LD] -- fill it back in on the way home. *)
Hypothesis PD0 : forall l h r,
  cstep tm (qD, (h :: l, S0, r)) = Some (qD, (l, h, S1 :: r)).
(** [0RB] -- close the trip, one cell further right than the last. *)
Hypothesis PD1 : forall l h r,
  cstep tm (qD, (l, S1, h :: r)) = Some (qB, (S0 :: l, h, r)).

Local Ltac go H := erewrite (stepR tm _ _ _ (H _ _ _)).
Local Ltac gorun H := erewrite (stepN tm _ _ _ _ H).

(** [qA] walks LEFT over a run of ones, writing them back. *)
Lemma P_sweepA : forall k l h r,
  csteps tm (S k) (qA, (rep [S1] k ++ h :: l, S1, r))
    = Some (qA, (l, h, rep [S1] (S k) ++ r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go PA1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go PA1. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** [qC] walks RIGHT over the run, BLANKING it. *)
Lemma P_sweepC : forall k l h r,
  csteps tm (S k) (qC, (l, S1, rep [S1] k ++ h :: r))
    = Some (qC, (rep [S0] (S k) ++ l, h, r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go PC1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go PC1. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** [qD] walks LEFT over the blanks [qC] just laid, filling them in. *)
Lemma P_sweepD : forall k l h r,
  csteps tm (S k) (qD, (rep [S0] k ++ h :: l, S0, r))
    = Some (qD, (l, h, rep [S1] (S k) ++ r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go PD0. reflexivity.
  - rewrite rep1_cons. cbn [app]. go PD0. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** One round trip: the hole moves one cell toward the head and the run
    ahead of it is one shorter. *)
Lemma P_hop : forall m X,
  csteps tm (2 * m + 5) (qB, (X, S1, rep [S1] (S m) ++ [S0]))
    = Some (qB, (S0 :: X, S1, rep [S1] m ++ [S0])).
Proof.
  intros m X. rewrite rep1_cons. cbn [app].
  replace (2 * m + 5) with (S (S m + S (S m + S 0))) by lia.
  go PB1.
  gorun (P_sweepC m (S1 :: X) S0 []).
  rewrite rep1_cons. cbn [app]. go PC0.
  gorun (P_sweepD m X S1 [S0]).
  rewrite rep1_cons. cbn [app]. go PD1. reflexivity.
Qed.

(** The last trip has no run left to cross. *)
Lemma P_term : forall X,
  csteps tm 3 (qB, (X, S1, [S0])) = Some (qB, (S0 :: X, S0, [])).
Proof. intros X. go PB1. go PC0. go PD1. reflexivity. Qed.

(** [m] round trips and the terminal: the run is gone. *)
Lemma P_bounce : forall m X,
  csteps tm (m * m + 4 * m + 3) (qB, (X, S1, rep [S1] m ++ [S0]))
    = Some (qB, (S0 :: rep [S0] m ++ X, S0, [])).
Proof.
  induction m as [|m IH]; intros X.
  - apply P_term.
  - replace (S m * S m + 4 * S m + 3) with ((2 * m + 5) + (m * m + 4 * m + 3))
      by lia.
    gorun (P_hop m X). rewrite IH, rep1_snoc. reflexivity.
Qed.

(** An even anchor: no carry run, so the low digit just flips. *)
Lemma P_lap0 : forall W,
  csteps tm 2 (qB, (S0 :: W, S0, [])) = Some (qB, (S1 :: W, S0, [])).
Proof. intros W. go PB0. go PA0. reflexivity. Qed.

(** The lap: one increment, uniformly in the deep word. *)
Lemma P_lap : forall j W,
  csteps tm ((j + 1) * (j + 2)) (qB, (rep [S1] j ++ S0 :: W, S0, []))
    = Some (qB, (rep [S0] j ++ S1 :: W, S0, [])).
Proof.
  intros [|j] W.
  - replace ((0 + 1) * (0 + 2)) with 2 by lia. cbn [rep app]. apply P_lap0.
  - rewrite rep1_cons. cbn [app].
    replace ((S j + 1) * (S j + 2)) with (S (S j + S (j * j + 4 * j + 3)))
      by lia.
    go PB0.
    gorun (P_sweepA j W S0 [S0]).
    rewrite rep1_cons. cbn [app]. go PA0.
    rewrite P_bounce. reflexivity.
Qed.

(** ** Visits

    [qB] and [qA] sit at the anchor; [qC] and [qD] are the round trip,
    which a carry run of length zero never starts. *)
Lemma P_entry : forall j W,
  csteps tm (S (S j + S 0)) (qB, (rep [S1] (S j) ++ S0 :: W, S0, []))
    = Some (qB, (S1 :: W, S1, rep [S1] j ++ [S0])).
Proof.
  intros j W. rewrite rep1_cons. cbn [app].
  go PB0.
  gorun (P_sweepA j W S0 [S0]).
  rewrite rep1_cons. cbn [app]. go PA0. reflexivity.
Qed.

Lemma P_trip : forall X j,
  (exists k c, csteps tm k (qB, (X, S1, rep [S1] j ++ [S0])) = Some c
               /\ fst c = qC)
  /\ (exists k c, csteps tm k (qB, (X, S1, rep [S1] j ++ [S0])) = Some c
                  /\ fst c = qD).
Proof.
  intros X j. destruct j as [|j].
  - cbn [rep app]. split.
    + exists 1. eexists. split; [go PB1; reflexivity | reflexivity].
    + exists 2. eexists. split; [go PB1; go PC0; reflexivity | reflexivity].
  - rewrite rep1_cons. cbn [app]. split.
    + exists 1. eexists. split; [go PB1; reflexivity | reflexivity].
    + exists (S (S j + S 0)). eexists. split.
      * go PB1.
        gorun (P_sweepC j (S1 :: X) S0 []).
        rewrite rep1_cons. cbn [app]. go PC0. reflexivity.
      * reflexivity.
Qed.

Lemma P_vis : forall j W q,
  exists k c, csteps tm k (qB, (rep [S1] (S j) ++ S0 :: W, S0, [])) = Some c
              /\ fst c = q.
Proof.
  intros j W q.
  destruct (rep_cons_ne S1 (S j) S0 W) as (h & t & Hne).
  destruct (Hcover q) as [-> | [-> | [-> | ->]]].
  - (* qA: one step in *)
    exists 1. rewrite Hne. eexists. split; [go PB0; reflexivity | reflexivity].
  - (* qB: at the anchor *)
    exists 0. eexists. split; reflexivity.
  - (* qC, qD: inside the first round trip *)
    destruct (proj1 (P_trip (S1 :: W) j)) as (k & c & Hk & Hq).
    exists (S (S j + S 0) + k), c. split; [|exact Hq].
    rewrite csteps_add, P_entry. exact Hk.
  - destruct (proj2 (P_trip (S1 :: W) j)) as (k & c & Hk & Hq).
    exists (S (S j + S 0) + k), c. split; [|exact Hq].
    rewrite csteps_add, P_entry. exact Hk.
Qed.

(** ** The anchor family and the closer *)

Definition PCf (p : positive) : cconf := (qB, (Kp p ++ [S0], S0, [])).

Theorem P_neverqh : forall p0,
  (exists t0, stepn tm t0 InitES = Some (lift (PCf p0))) ->
  NeverQuasiHaltsSt tm.
Proof.
  intros p0 Hboot. apply (glue_neverqh tm PCf p0).
  - exact Hboot.
  - intros p _. unfold PCf.
    destruct (Kp_lap_split p) as (j & W & Hsplit & Hnext & _).
    exists ((j + 1) * (j + 2)), (qB, (rep [S0] j ++ S1 :: W, S0, [])).
    split; [rewrite Hsplit; apply P_lap|].
    split; [exact (lift_pad_eq qB [] _ _ Hnext) | nia].
  - intros p q _. unfold PCf.
    destruct (Kp_lap_split p) as (j & W & Hsplit & _ & Hzero).
    rewrite Hsplit. destruct j as [|j]; [|apply P_vis].
    destruct (Hzero eq_refl) as (j2 & W2 & HW).
    destruct (P_vis j2 W2 q) as (k & c & Hk & Hq).
    exists (2 + k), c. split; [|exact Hq].
    cbn [rep app]. rewrite csteps_add, P_lap0, HW. exact Hk.
Qed.

End Plain.

(** * The SPACER shape: a blank between counter and head, and the hole
      runs away from it *)

Section Spacer.

Variable tm : TM.
Variable qA qB qC qD : St.

Hypothesis Hcover : forall q : St, q = qA \/ q = qB \/ q = qC \/ q = qD.

(** [1RB] -- the stop digit is set and the sweep out begins. *)
Hypothesis SA0 : forall l h r,
  cstep tm (qA, (l, S0, h :: r)) = Some (qB, (S1 :: l, h, r)).
(** [0LD] -- open the hole. *)
Hypothesis SA1 : forall l h r,
  cstep tm (qA, (h :: l, S1, r)) = Some (qD, (l, h, S0 :: r)).
(** [0LC] -- the anchor's turnaround, across the spacer. *)
Hypothesis SB0 : forall l h r,
  cstep tm (qB, (h :: l, S0, r)) = Some (qC, (l, h, S0 :: r)).
(** [0RB] -- blank the finished run. *)
Hypothesis SB1 : forall l h r,
  cstep tm (qB, (l, S1, h :: r)) = Some (qB, (S0 :: l, h, r)).
(** [1LA] -- fill the hole and turn back. *)
Hypothesis SC0 : forall l h r,
  cstep tm (qC, (h :: l, S0, r)) = Some (qA, (l, h, S1 :: r)).
(** [1RC] -- walk right over the run, leaving it alone. *)
Hypothesis SC1 : forall l h r,
  cstep tm (qC, (l, S1, h :: r)) = Some (qC, (S1 :: l, h, r)).
(** [0RC] -- the far turn of a round trip. *)
Hypothesis SD0 : forall l h r,
  cstep tm (qD, (l, S0, h :: r)) = Some (qC, (S0 :: l, h, r)).
(** [1LD] -- walk left over the run, leaving it alone. *)
Hypothesis SD1 : forall l h r,
  cstep tm (qD, (h :: l, S1, r)) = Some (qD, (l, h, S1 :: r)).

Local Ltac go H := erewrite (stepR tm _ _ _ (H _ _ _)).
Local Ltac gorun H := erewrite (stepN tm _ _ _ _ H).

Lemma S_sweepD : forall k l h r,
  csteps tm (S k) (qD, (rep [S1] k ++ h :: l, S1, r))
    = Some (qD, (l, h, rep [S1] (S k) ++ r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go SD1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go SD1. rewrite IH, rep1_snoc. reflexivity.
Qed.

Lemma S_sweepC : forall k l h r,
  csteps tm (S k) (qC, (l, S1, rep [S1] k ++ h :: r))
    = Some (qC, (rep [S1] (S k) ++ l, h, r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go SC1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go SC1. rewrite IH, rep1_snoc. reflexivity.
Qed.

Lemma S_sweepB : forall k l h r,
  csteps tm (S k) (qB, (l, S1, rep [S1] k ++ h :: r))
    = Some (qB, (rep [S0] (S k) ++ l, h, r)).
Proof.
  induction k as [|k IH]; intros l h r.
  - cbn [rep app]. go SB1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go SB1. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** The probe: [k] cells of the run crossed and refilled on the head's
    side of the hole, [m] still ahead of it. *)
Definition SP (k m : nat) (X : list Sym) : cconf :=
  (qA, (rep [S1] m ++ S0 :: X, S1, rep [S1] (S k) ++ [S0])).

(** One round trip drives the hole one cell deeper. *)
Lemma S_hop : forall k m X,
  csteps tm (2 * m + 5) (SP k (S m) X) = Some (SP (S k) m X).
Proof.
  intros k m X. unfold SP.
  rewrite (rep1_cons S1 m). cbn [app].
  replace (2 * m + 5) with (S (S m + S (S m + S 0))) by lia.
  go SA1.
  gorun (S_sweepD m X S0 (S0 :: rep [S1] (S k) ++ [S0])).
  rewrite (rep1_cons S1 m). cbn [app]. go SD0.
  gorun (S_sweepC m (S0 :: X) S0 (rep [S1] (S k) ++ [S0])).
  rewrite (rep1_cons S1 m). cbn [app]. go SC0. reflexivity.
Qed.

(** The hole reaches the stop digit: it is SET, and the run -- solid ones
    again -- is blanked in one sweep. *)
Lemma S_term : forall k X,
  csteps tm (k + 6) (SP k 0 X)
    = Some (qB, (rep [S0] (S (S k)) ++ S1 :: X, S0, [])).
Proof.
  intros k X. unfold SP. cbn [rep app].
  replace (k + 6) with (S (S (S (S (S (S k)))))) by lia.
  go SA1. go SD0. go SC0. go SA0.
  exact (S_sweepB (S k) (S1 :: X) S0 []).
Qed.

Lemma S_bounce : forall m k X,
  csteps tm (m * m + 5 * m + k + 6) (SP k m X)
    = Some (qB, (rep [S0] (S (S (k + m))) ++ S1 :: X, S0, [])).
Proof.
  induction m as [|m IH]; intros k X.
  - replace (k + 0) with k by lia.
    replace (0 * 0 + 5 * 0 + k + 6) with (k + 6) by lia.
    apply S_term.
  - replace (S m * S m + 5 * S m + k + 6)
       with ((2 * m + 5) + (m * m + 5 * m + S k + 6)) by lia.
    gorun (S_hop k m X). rewrite IH.
    replace (S k + m) with (k + S m) by lia. reflexivity.
Qed.

Lemma S_lap0 : forall W,
  csteps tm 4 (qB, (S0 :: S0 :: W, S0, [])) = Some (qB, (S0 :: S1 :: W, S0, [])).
Proof. intros W. go SB0. go SC0. go SA0. go SB1. reflexivity. Qed.

Lemma S_lap : forall j W,
  csteps tm (j * j + 3 * j + 4) (qB, (S0 :: rep [S1] j ++ S0 :: W, S0, []))
    = Some (qB, (S0 :: rep [S0] j ++ S1 :: W, S0, [])).
Proof.
  intros [|j] W.
  - replace (0 * 0 + 3 * 0 + 4) with 4 by lia. cbn [rep app]. apply S_lap0.
  - replace (S j * S j + 3 * S j + 4) with (S (S (j * j + 5 * j + 0 + 6)))
      by lia.
    go SB0.
    rewrite (rep1_cons S1 j). cbn [app]. go SC0.
    change (S1 :: [S0]) with (rep [S1] 1 ++ [S0]).
    exact (S_bounce j 0 W).
Qed.

(** [qB], [qC] and [qA] in the first three steps of any lap; [qD] on the
    fourth, which needs the carry run to be non-empty. *)
Lemma S_vis : forall j W q,
  exists k c,
    csteps tm k (qB, (S0 :: rep [S1] (S j) ++ S0 :: W, S0, [])) = Some c
    /\ fst c = q.
Proof.
  intros j W q. rewrite (rep1_cons S1 j). cbn [app].
  destruct (rep_cons_ne S1 j S0 W) as (h & t & Hne).
  destruct (Hcover q) as [-> | [-> | [-> | ->]]].
  - exists 2. eexists. split; [go SB0; go SC0; reflexivity | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [go SB0; reflexivity | reflexivity].
  - exists 3. rewrite Hne. eexists.
    split; [go SB0; go SC0; go SA1; reflexivity | reflexivity].
Qed.

(** ** The anchor family and the closer *)

Definition SCf (p : positive) : cconf := (qB, (S0 :: (Kp p ++ [S0]), S0, [])).

Theorem S_neverqh : forall p0,
  (exists t0, stepn tm t0 InitES = Some (lift (SCf p0))) ->
  NeverQuasiHaltsSt tm.
Proof.
  intros p0 Hboot. apply (glue_neverqh tm SCf p0).
  - exact Hboot.
  - intros p _. unfold SCf.
    destruct (Kp_lap_split p) as (j & W & Hsplit & Hnext & _).
    exists (j * j + 3 * j + 4), (qB, (S0 :: rep [S0] j ++ S1 :: W, S0, [])).
    split; [rewrite Hsplit; apply S_lap|].
    split; [exact (lift_pad_eq qB [S0] _ _ Hnext) | nia].
  - intros p q _. unfold SCf.
    destruct (Kp_lap_split p) as (j & W & Hsplit & _ & Hzero).
    rewrite Hsplit. destruct j as [|j]; [|apply S_vis].
    destruct (Hzero eq_refl) as (j2 & W2 & HW).
    destruct (S_vis j2 W2 q) as (k & c & Hk & Hq).
    exists (4 + k), c. split; [|exact Hq].
    cbn [rep app]. rewrite csteps_add, S_lap0, HW. exact Hk.
Qed.

End Spacer.
