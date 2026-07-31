(** * TernCounter: BASE-THREE counter numerals, and their digit alphabet.

    Every counter alphabet in this development ([ILCounter.Ip],
    [JpCounter.Jp], [KpCounter.Kp], [DpCounter.Dp], [MpCounter.Mp],
    [BpCounter.Bp], and every generated [Alph_*]) is BASE 2: they are
    indexed by [positive], and [MonoCounter.cview] reads the carry as the run
    of low SET bits.  So is every measurement tool -- [tools/kcopy_classify.py]
    speaks of "one bit per k cells" and [tools/counters/alphabet_infer.py] is
    a positive-recursion.

    Part of the residue is not base 2.  [tools/counters/radix_infer.py] reads
    [1RB---_0LB1RC_0RD0RC_1LB1LD] as a base-3 counter -- after the wall the
    tape is 2-cell digits over {00, 01, 11}, the anchor snapshots decode to
    1, 2, 3, ... consecutively over 10^4 visits, and the lap is [4j + 4] in
    the carry length.  Read at base 2 the same row looks like a
    [Theta(3^j)] "EXP3", which is why every base-2 emitter bounces off it.

    This file is the base-3 twin of [KpCounter] + [MonoCounter.cview]:

    - [tern], numerals with digits 0/1/2, LOW digit outermost, [tE] the end
      of the numeral (so a numeral need not be canonical -- leading zeros are
      harmless here, and nothing downstream inspects the value);
    - [tview t = (j, r)]: [j] is the length of the low run of 2s and [r]
      names the digit that stops it ([None] = the run reaches the end of the
      numeral, i.e. overflow);
    - [Tw], the word on the tape, over three digit words [A0]/[A1]/[A2] and a
      TERMINATOR [C] -- exactly the [E xH = C], [E (xO q) = A ++ E q] shape
      of the base-2 alphabets, one digit wider;
    - two increments, [tsucc] (no terminator: overflow appends a fresh digit
      1) and [tsuccT] (a terminator sits past the top digit and stays there:
      overflow appends a fresh digit 0 instead).  Both occur among the
      three-state core rows.

    [ter_step] packages what a lap proof actually consumes: ONE trichotomy,
    stated in single cells rather than digits, covering both increments.  It
    is PROVED rather than assumed, so a wrong digit triple fails to typecheck
    instead of mis-proving.

    Axiom footprint: none. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** Numerals *)

Inductive tern : Set :=
| tE                       (* end of the numeral *)
| tD0 (t : tern)           (* digit 0, low end *)
| tD1 (t : tern)
| tD2 (t : tern).

(** No terminator: the carry runs off the end and writes a fresh digit 1. *)
Fixpoint tsucc (t : tern) : tern :=
  match t with
  | tE => tD1 tE
  | tD0 t' => tD1 t'
  | tD1 t' => tD2 t'
  | tD2 t' => tD0 (tsucc t')
  end.

(** With a terminator past the top digit, the carry stops ON it and the
    fresh digit is a 0 -- the terminator itself is what got carried. *)
Fixpoint tsuccT (t : tern) : tern :=
  match t with
  | tE => tD0 tE
  | tD0 t' => tD1 t'
  | tD1 t' => tD2 t'
  | tD2 t' => tD0 (tsuccT t')
  end.

Fixpoint tview (t : tern) : nat * option (bool * tern) :=
  match t with
  | tE => (0, None)
  | tD0 t' => (0, Some (false, t'))
  | tD1 t' => (0, Some (true, t'))
  | tD2 t' => let (j, r) := tview t' in (S j, r)
  end.

Section Alphabet.

(** The three digit words and the terminator, low cell first. *)
Variable A0 A1 A2 C : list Sym.

Fixpoint Tw (t : tern) : list Sym :=
  match t with
  | tE => C
  | tD0 t' => A0 ++ Tw t'
  | tD1 t' => A1 ++ Tw t'
  | tD2 t' => A2 ++ Tw t'
  end.

(** Interior, stop digit 0: the run of 2s becomes a run of 0s and the stop
    digit steps 0 -> 1.  The carry never reaches [tE], so the two increments
    agree here. *)
Lemma tview_some0 : forall t j t', tview t = (j, Some (false, t')) ->
  Tw t = rep A2 j ++ A0 ++ Tw t' /\
  Tw (tsucc t) = rep A0 j ++ A1 ++ Tw t' /\
  Tw (tsuccT t) = rep A0 j ++ A1 ++ Tw t'.
Proof.
  induction t as [|t IH|t IH|t IH]; intros j t' H; cbn in H.
  - discriminate.
  - injection H as <- <-. repeat split; reflexivity.
  - discriminate.
  - destruct (tview t) as [j0 r]. injection H as Hj Hr; subst j.
    destruct (IH j0 t' ltac:(rewrite Hr; reflexivity)) as (H1 & H2 & H3).
    cbn [Tw tsucc tsuccT rep]. rewrite H1, H2, H3, <- !app_assoc.
    repeat split; reflexivity.
Qed.

(** Interior, stop digit 1: same run, and the stop digit steps 1 -> 2. *)
Lemma tview_some1 : forall t j t', tview t = (j, Some (true, t')) ->
  Tw t = rep A2 j ++ A1 ++ Tw t' /\
  Tw (tsucc t) = rep A0 j ++ A2 ++ Tw t' /\
  Tw (tsuccT t) = rep A0 j ++ A2 ++ Tw t'.
Proof.
  induction t as [|t IH|t IH|t IH]; intros j t' H; cbn in H.
  - discriminate.
  - discriminate.
  - injection H as <- <-. repeat split; reflexivity.
  - destruct (tview t) as [j0 r]. injection H as Hj Hr; subst j.
    destruct (IH j0 t' ltac:(rewrite Hr; reflexivity)) as (H1 & H2 & H3).
    cbn [Tw tsucc tsuccT rep]. rewrite H1, H2, H3, <- !app_assoc.
    repeat split; reflexivity.
Qed.

(** Overflow: the numeral is [j] digits of 2 over the terminator.  This is
    the one place the two increments part company. *)
Lemma tview_none : forall t j, tview t = (j, None) ->
  Tw t = rep A2 j ++ C /\
  Tw (tsucc t) = rep A0 j ++ A1 ++ C /\
  Tw (tsuccT t) = rep A0 j ++ A0 ++ C.
Proof.
  induction t as [|t IH|t IH|t IH]; intros j H; cbn in H.
  - injection H as <-. cbn. repeat split; reflexivity.
  - discriminate.
  - discriminate.
  - destruct (tview t) as [j0 r]. injection H as Hj Hr; subst j.
    destruct (IH j0 ltac:(rewrite Hr; reflexivity)) as (H1 & H2 & H3).
    cbn [Tw tsucc tsuccT rep]. rewrite H1, H2, H3, <- !app_assoc.
    repeat split; reflexivity.
Qed.

End Alphabet.

(** ** The trichotomy a lap proof consumes

    Stated in SINGLE CELLS: the carry run is [rep [S1] m] whatever the digit
    width, the stop is a two-cell [00] or [01], and overflow is a bare run.
    [Counters/Ter3Wall.v] takes exactly this and nothing else about the
    numerals, which is what lets one closer serve both increments. *)

Definition TerStep (Wf : tern -> list Sym) (nx : tern -> tern) : Prop :=
  forall t,
    (exists m u, Wf t = rep [S1] m ++ [S0; S0] ++ u
            /\ Wf (nx t) = rep [S0] (S m) ++ [S1] ++ u)
    \/ (exists m u, Wf t = rep [S1] m ++ [S0; S1] ++ u
              /\ Wf (nx t) = rep [S0] m ++ [S1; S1] ++ u)
    \/ (exists m, Wf t = rep [S1] m
            /\ Wf (nx t) = rep [S0] (S m) ++ [S1]).

(** The concrete digit words of the three-state core rows. *)
Notation D0 := [S0; S0].
Notation D1 := [S0; S1].
Notation D2 := [S1; S1].

Lemma rep_two : forall (x : Sym) k, rep [x; x] k = rep [x] (k + k).
Proof.
  induction k as [|k IH]; [reflexivity |].
  replace (S k + S k) with (S (S (k + k))) by lia.
  cbn [rep]. rewrite IH. reflexivity.
Qed.

Lemma rep_succ_r : forall (x : Sym) k l,
  rep [x] k ++ x :: l = rep [x] (S k) ++ l.
Proof.
  intros x k l. cbn [rep app].
  change (x :: l) with ([x] ++ l). rewrite app_assoc, rep_shift.
  rewrite <- app_assoc. reflexivity.
Qed.

(** The no-terminator scheme. *)
Lemma ter_step_nil : TerStep (Tw D0 D1 D2 []) tsucc.
Proof.
  intro t. destruct (tview t) as [j r] eqn:Ev. destruct r as [[b t']|].
  - destruct b.
    + right; left. exists (j + j), (Tw D0 D1 D2 [] t').
      destruct (tview_some1 D0 D1 D2 [] t j t' Ev) as (H1 & H2 & _).
      rewrite H1, H2, !rep_two. split; reflexivity.
    + left. exists (j + j), (Tw D0 D1 D2 [] t').
      destruct (tview_some0 D0 D1 D2 [] t j t' Ev) as (H1 & H2 & _).
      rewrite H1, H2, !rep_two. split; [reflexivity |].
      cbn [app]. rewrite rep_succ_r. reflexivity.
  - right; right. exists (j + j).
    destruct (tview_none D0 D1 D2 [] t j Ev) as (H1 & H2 & _).
    rewrite H1, H2, !rep_two, !app_nil_r. split; [reflexivity |].
    cbn [app]. rewrite rep_succ_r. reflexivity.
Qed.

(** The terminator scheme: a single [S1] sits past the top digit, and the
    overflow carry clears it too -- so the run is ODD, and the fresh digit
    the increment writes is a 0 with the terminator restored past it. *)
Lemma ter_step_one : TerStep (Tw D0 D1 D2 [S1]) tsuccT.
Proof.
  intro t. destruct (tview t) as [j r] eqn:Ev. destruct r as [[b t']|].
  - destruct b.
    + right; left. exists (j + j), (Tw D0 D1 D2 [S1] t').
      destruct (tview_some1 D0 D1 D2 [S1] t j t' Ev) as (H1 & _ & H3).
      rewrite H1, H3, !rep_two. split; reflexivity.
    + left. exists (j + j), (Tw D0 D1 D2 [S1] t').
      destruct (tview_some0 D0 D1 D2 [S1] t j t' Ev) as (H1 & _ & H3).
      rewrite H1, H3, !rep_two. split; [reflexivity |].
      cbn [app]. rewrite rep_succ_r. reflexivity.
  - right; right. exists (S (j + j)).
    destruct (tview_none D0 D1 D2 [S1] t j Ev) as (H1 & _ & H3).
    rewrite H1, H3, !rep_two. split.
    + cbn [app]. rewrite rep_succ_r, app_nil_r. reflexivity.
    + cbn [app]. rewrite !rep_succ_r. reflexivity.
Qed.
