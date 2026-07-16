(** * Records: extent bounds and the blank-beyond-the-record invariant.

    The fuel / drift reduction rules ((c2), (c3) in the harness's
    [neverqh.md]) rest on a single geometric fact that the head-relative
    machine model does not make syntactically obvious: a run that starts
    on the blank tape can only have deposited nonblank cells inside the
    interval the head has actually visited, and that interval grows by at
    most one cell per step.  Equivalently, on each side of the head the
    nonblank cells lie within a bounded window, and a step that moves the
    head TOWARD a side shrinks that side's window.

    This is exactly the substrate SCOPING §4 calls "record events and
    extents ... cells strictly beyond the all-time extent are blank ...
    the shared substrate of tcycler, (c3) and (c4)".  It is proved here
    once, purely on the abstract [Tape]/[step]/[stepn] semantics, so the
    fuel abstraction and the (c2)/(c3) liveness arguments can consume it
    without re-deriving any tape algebra.

    The key consequence for rule (c2): a run confined to a right-moving
    ("runner") phase drives the right window to 0 in finitely many steps
    ([run_right_exhausts]); once the window is 0 the entire right half-tape
    is blank, so a "fuel >= 1 on the movement side" invariant is
    impossible to maintain forever. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

(** ** Side windows

    [right_bounded tp R]: every cell on the right half-tape at offset [R]
    or beyond is blank, i.e. all nonblank right cells lie in offsets
    [0..R-1].  [left_bounded] is the mirror.  These are the "extent"
    predicates: [R] (resp. [L]) is an upper bound on how far the run has
    reached to the right (resp. left) of the current head. *)

Definition right_bounded (tp : Tape) (R : nat) : Prop :=
  forall j, R <= j -> t_right tp j = S0.

Definition left_bounded (tp : Tape) (L : nat) : Prop :=
  forall j, L <= j -> t_left tp j = S0.

Lemma right_bounded_mono : forall tp R R',
  R <= R' -> right_bounded tp R -> right_bounded tp R'.
Proof. intros tp R R' Hle H j Hj. apply H. lia. Qed.

Lemma left_bounded_mono : forall tp L L',
  L <= L' -> left_bounded tp L -> left_bounded tp L'.
Proof. intros tp L L' Hle H j Hj. apply H. lia. Qed.

(** ** One [tape_move] step, per direction

    Moving right shrinks the right window (a cell is crossed) and grows
    the left window by at most one (the written cell is deposited just
    behind the head).  Moving left is the mirror. *)

Lemma move_DR_right : forall w tp R,
  right_bounded tp R -> right_bounded (tape_move DR w tp) (Nat.pred R).
Proof.
  intros w tp R H j Hj. simpl. unfold tail_side.
  apply H. lia.
Qed.

Lemma move_DR_left : forall w tp L,
  left_bounded tp L -> left_bounded (tape_move DR w tp) (S L).
Proof.
  intros w tp L H j Hj. simpl. unfold push_side.
  destruct j as [|j']; [lia|]. apply H. lia.
Qed.

Lemma move_DL_left : forall w tp L,
  left_bounded tp L -> left_bounded (tape_move DL w tp) (Nat.pred L).
Proof.
  intros w tp L H j Hj. simpl. unfold tail_side.
  apply H. lia.
Qed.

Lemma move_DL_right : forall w tp R,
  right_bounded tp R -> right_bounded (tape_move DL w tp) (S R).
Proof.
  intros w tp R H j Hj. simpl. unfold push_side.
  destruct j as [|j']; [lia|]. apply H. lia.
Qed.

(** ** One [step]: both windows grow by at most one.

    The coarse bound used for the from-blank extent lemma. *)

Lemma step_bounded : forall tm q tp q' tp' R L,
  step tm (q, tp) = Some (q', tp') ->
  right_bounded tp R -> left_bounded tp L ->
  right_bounded tp' (S R) /\ left_bounded tp' (S L).
Proof.
  intros tm q tp q' tp' R L Hstep HR HL.
  unfold step in Hstep.
  destruct (tm q (t_head tp)) as [tr|] eqn:E; [|discriminate].
  injection Hstep as _ <-.
  destruct (t_dir tr) eqn:Ed.
  - (* DL: right grows, left shrinks *)
    split.
    + apply move_DL_right; exact HR.
    + apply (left_bounded_mono _ (Nat.pred L)); [lia|].
      apply move_DL_left; exact HL.
  - (* DR: right shrinks, left grows *)
    split.
    + apply (right_bounded_mono _ (Nat.pred R)); [lia|].
      apply move_DR_right; exact HR.
    + apply move_DR_left; exact HL.
Qed.

(** ** Iterated: after [n] steps from a config bounded by [(R, L)],
    the reached config is bounded by [(R + n, L + n)]. *)

Lemma stepn_bounded : forall tm n q tp c' R L,
  stepn tm n (q, tp) = Some c' ->
  right_bounded tp R -> left_bounded tp L ->
  right_bounded (snd c') (R + n) /\ left_bounded (snd c') (L + n).
Proof.
  induction n as [|n IH]; intros q tp c' R L Hrun HR HL.
  - simpl in Hrun. injection Hrun as <-. simpl.
    rewrite !Nat.add_0_r. split; assumption.
  - cbn [stepn] in Hrun.
    destruct (step tm (q, tp)) as [[q1 tp1]|] eqn:E; [|discriminate].
    destruct (step_bounded _ _ _ _ _ _ _ E HR HL) as [HR1 HL1].
    destruct (IH q1 tp1 c' (S R) (S L) Hrun HR1 HL1) as [HRn HLn].
    split.
    + apply (right_bounded_mono _ (S R + n)); [lia | exact HRn].
    + apply (left_bounded_mono _ (S L + n)); [lia | exact HLn].
Qed.

(** ** From the blank tape: extent <= step count.

    The classic record fact: after [n] steps from the initial blank
    configuration, every cell at offset [n] or beyond -- on either side
    of the head -- is blank.  [InitES] is bounded by [(0, 0)]. *)

Lemma init_right_bounded : right_bounded (snd InitES) 0.
Proof. intros j _. reflexivity. Qed.

Lemma init_left_bounded : left_bounded (snd InitES) 0.
Proof. intros j _. reflexivity. Qed.

Theorem extent_le_steps : forall tm n c,
  stepn tm n InitES = Some c ->
  right_bounded (snd c) n /\ left_bounded (snd c) n.
Proof.
  intros tm n c Hrun.
  destruct (stepn_bounded tm n StA (mkTape blank_side S0 blank_side) c 0 0
              Hrun init_right_bounded init_left_bounded) as [HR HL].
  rewrite Nat.add_0_l in HR, HL. split; assumption.
Qed.

(** ** The runner: a toward-side move exhausts that side's window.

    [n] consecutive right-moves shrink the right window by [n] (nat
    truncated).  So from a config with right window [R], after [R] steps
    of a right-runner the right half-tape is entirely blank -- the fact
    that makes a "fuel >= 1 on the movement side, forever" invariant
    impossible under rule (c2).

    The hypothesis [right_runner] abstracts "every step in the stretch
    moves the head right"; it is what an alive intra-SCC edge set of a
    right-moving runner SCC guarantees. *)

Definition steps_right (tm : TM) (c : ExecState) : Prop :=
  exists tr, tm (fst c) (t_head (snd c)) = Some tr /\ t_dir tr = DR.

Lemma step_right_shrinks : forall tm q tp q' tp' R,
  step tm (q, tp) = Some (q', tp') ->
  (exists tr, tm q (t_head tp) = Some tr /\ t_dir tr = DR) ->
  right_bounded tp R -> right_bounded tp' (Nat.pred R).
Proof.
  intros tm q tp q' tp' R Hstep [tr [Etm Ed]] HR.
  unfold step in Hstep. rewrite Etm in Hstep.
  injection Hstep as _ <-. rewrite Ed.
  apply move_DR_right; exact HR.
Qed.

(** If every configuration along an [n]-step run moves the head right,
    the right window shrinks by [n]. *)
Fixpoint all_right (tm : TM) (n : nat) (c : ExecState) : Prop :=
  match n with
  | 0 => True
  | S m => steps_right tm c /\
           match step tm c with
           | Some c' => all_right tm m c'
           | None => True
           end
  end.

Lemma run_right_shrinks : forall tm n c c' R,
  stepn tm n c = Some c' ->
  all_right tm n c ->
  right_bounded (snd c) R ->
  right_bounded (snd c') (R - n).
Proof.
  induction n as [|n IH]; intros c c' R Hrun Hall HR.
  - simpl in Hrun. injection Hrun as <-. rewrite Nat.sub_0_r. exact HR.
  - cbn [stepn] in Hrun.
    destruct c as [q tp].
    destruct (step tm (q, tp)) as [[q1 tp1]|] eqn:E; [|discriminate].
    cbn [all_right] in Hall. destruct Hall as [Hsr Hall'].
    rewrite E in Hall'.
    assert (HR1 : right_bounded tp1 (Nat.pred R)).
    { apply (step_right_shrinks tm q tp q1 tp1 R E Hsr HR). }
    specialize (IH (q1, tp1) c' (Nat.pred R) Hrun Hall' HR1).
    apply (right_bounded_mono _ (Nat.pred R - n)); [lia | exact IH].
Qed.

(** The payoff for rule (c2): a right-runner confined for at least [R]
    steps reaches a configuration whose entire right half-tape is blank
    (right window 0). *)
Theorem run_right_exhausts : forall tm c c' R,
  right_bounded (snd c) R ->
  stepn tm R c = Some c' ->
  all_right tm R c ->
  right_bounded (snd c') 0.
Proof.
  intros tm c c' R HR Hrun Hall.
  pose proof (run_right_shrinks tm R c c' R Hrun Hall HR) as H.
  rewrite Nat.sub_diag in H. exact H.
Qed.

(** [right_bounded _ 0] literally means "the whole right half-tape is
    blank": the form the fuel invariant contradicts. *)
Lemma right_bounded_0_blank : forall tp j,
  right_bounded tp 0 -> t_right tp j = S0.
Proof. intros tp j H. apply H. lia. Qed.

(** ** The fuel invariant, semantically

    "Right fuel >= 1" means the right half-tape carries at least one
    nonblank cell.  It is exactly what an empty right window
    contradicts, so it cannot survive a right-runner (rule (c2)). *)

Definition has_right_nonblank (tp : Tape) : Prop :=
  exists j, t_right tp j <> S0.

Lemma right_bounded_0_no_nonblank : forall tp,
  right_bounded tp 0 -> ~ has_right_nonblank tp.
Proof. intros tp H [j Hj]. apply Hj. apply H. lia. Qed.

(** Contrapositive form used by the liveness argument: a nonblank on
    the right forces a nonzero right window. *)
Lemma has_right_nonblank_window_pos : forall tp R,
  right_bounded tp R -> has_right_nonblank tp -> 1 <= R.
Proof.
  intros tp R HR Hnb. destruct R as [|R']; [|lia].
  exfalso. apply (right_bounded_0_no_nonblank tp HR Hnb).
Qed.
