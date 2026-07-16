(** * FuelClass: capped sided nonblank lower-bound classes.

    The fuel refinement of the n-gram abstraction pairs each context
    with a capped count of the nonblank cells on each side of the head.
    The C verifier tracks the EXACT capped count; here we track a
    capped LOWER BOUND -- [F0] = no information, [F1] = at least one
    nonblank, [F2] = at least two -- which is all rule (c2) consumes
    ([node_rfuel_ge1] asserts only ">= 1"), and which makes every
    per-move transition a deterministic, constructive function with no
    excluded middle and no branching (the exact version needs a
    disjunctive split at the cap).

    A soundness-only weakening: a lower-bound class is a valid cover of
    any configuration with at least that many nonblanks, so the closure
    stays sound; it may catch fewer machines than exact tracking, never
    more.  The two facts the fuel abstraction needs are proved here:
    depositing a cell ([push_side], the write left behind a move)
    increments the class, and crossing a cell ([tail_side], the cell
    the head steps over) decrements it -- both by the crossed/written
    symbol read off the context. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

(** ** Classes and their semantics *)

Inductive fclass : Set := F0 | F1 | F2.

Definition nb (s : Sym) : bool := match s with S0 => false | S1 => true end.

Lemma nb_true : forall s, nb s = true -> s <> S0.
Proof. intros [] H; simpl in H; [discriminate | intro Hc; discriminate]. Qed.

Lemma nb_false : forall s, nb s = false -> s = S0.
Proof. intros [] H; [reflexivity | discriminate]. Qed.

(** At least one / at least two nonblank cells on a half side. *)
Definition side_ge1 (f : nat -> Sym) : Prop := exists j, f j <> S0.
Definition side_ge2 (f : nat -> Sym) : Prop :=
  exists i j, i < j /\ f i <> S0 /\ f j <> S0.

Lemma side_ge2_ge1 : forall f, side_ge2 f -> side_ge1 f.
Proof. intros f (i & j & _ & Hi & _). exists i; exact Hi. Qed.

(** The lower-bound meaning of a class. *)
Definition class_holds (fc : fclass) (f : nat -> Sym) : Prop :=
  match fc with
  | F0 => True
  | F1 => side_ge1 f
  | F2 => side_ge2 f
  end.

(** ">= 1 nonblank" as a boolean, and its soundness. *)
Definition fc_ge1 (fc : fclass) : bool :=
  match fc with F0 => false | F1 | F2 => true end.

Lemma fc_ge1_sound : forall fc f,
  class_holds fc f -> fc_ge1 fc = true -> side_ge1 f.
Proof.
  intros [] f H Hge; simpl in *; try discriminate.
  - exact H.
  - apply side_ge2_ge1; exact H.
Qed.

(** ** Deposit (push): a written cell can only raise the count *)

Definition finc (b : bool) (fc : fclass) : fclass :=
  if b then match fc with F0 => F1 | F1 => F2 | F2 => F2 end else fc.

Lemma push_ge1 : forall w f, w <> S0 -> side_ge1 (push_side w f).
Proof. intros w f Hw. exists 0. exact Hw. Qed.

Lemma push_side_ge1_iff_blank : forall w f, w = S0 ->
  (side_ge1 (push_side w f) <-> side_ge1 f).
Proof.
  intros w f ->; split.
  - intros [j Hj]. destruct j as [|j']; [simpl in Hj; congruence|].
    exists j'; exact Hj.
  - intros [j Hj]. exists (S j); exact Hj.
Qed.

Lemma push_side_ge2_blank : forall f, side_ge2 f -> side_ge2 (push_side S0 f).
Proof.
  intros f (i & j & Hij & Hi & Hj).
  exists (S i), (S j). repeat split; [lia | exact Hi | exact Hj].
Qed.

(** A nonblank write plus an existing nonblank makes two. *)
Lemma push_side_ge2_nonblank : forall w f, w <> S0 ->
  side_ge1 f -> side_ge2 (push_side w f).
Proof.
  intros w f Hw [j Hj].
  exists 0, (S j). repeat split; [lia | exact Hw | exact Hj].
Qed.

Theorem finc_sound : forall w fc f,
  class_holds fc f -> class_holds (finc (nb w) fc) (push_side w f).
Proof.
  intros w fc f H.
  destruct (nb w) eqn:Enb; simpl.
  - (* nonblank write *)
    assert (Hw : w <> S0) by (apply nb_true; exact Enb).
    destruct fc; simpl in H |- *.
    + apply push_ge1; exact Hw.
    + apply push_side_ge2_nonblank; [exact Hw | exact H].
    + apply push_side_ge2_nonblank; [exact Hw | apply side_ge2_ge1; exact H].
  - (* blank write: class unchanged *)
    assert (Hw : w = S0) by (apply nb_false; exact Enb).
    destruct fc; simpl in H |- *.
    + exact I.
    + apply (push_side_ge1_iff_blank w f Hw); exact H.
    + subst w. apply push_side_ge2_blank; exact H.
Qed.

(** ** Cross (tail): stepping over a cell can only lower the count *)

Definition fdec (b : bool) (fc : fclass) : fclass :=
  if b then match fc with F0 => F0 | F1 => F0 | F2 => F1 end else fc.

Lemma tail_ge1_blank : forall f, f 0 = S0 -> side_ge1 f -> side_ge1 (tail_side f).
Proof.
  intros f H0 [j Hj]. destruct j as [|j'].
  - congruence.
  - exists j'. unfold tail_side. exact Hj.
Qed.

Lemma tail_ge2_blank : forall f, f 0 = S0 -> side_ge2 f -> side_ge2 (tail_side f).
Proof.
  intros f H0 (i & j & Hij & Hi & Hj).
  destruct i as [|i'], j as [|j']; try congruence.
  exists i', j'. unfold tail_side. repeat split; [lia | exact Hi | exact Hj].
Qed.

Lemma tail_ge1_of_ge2 : forall f, side_ge2 f -> side_ge1 (tail_side f).
Proof.
  intros f (i & j & Hij & _ & Hj).
  destruct j as [|j']; [lia|].
  exists j'. unfold tail_side. exact Hj.
Qed.

Theorem fdec_sound : forall fc f,
  class_holds fc f -> class_holds (fdec (nb (f 0)) fc) (tail_side f).
Proof.
  intros fc f H.
  destruct (nb (f 0)) eqn:Enb; simpl.
  - (* crossed a nonblank: lower bound drops by one *)
    destruct fc; simpl in H |- *.
    + exact I.
    + exact I.
    + apply tail_ge1_of_ge2; exact H.
  - (* crossed a blank: class unchanged *)
    assert (H0 : f 0 = S0) by (apply nb_false; exact Enb).
    destruct fc; simpl in H |- *.
    + exact I.
    + apply tail_ge1_blank; [exact H0 | exact H].
    + apply tail_ge2_blank; [exact H0 | exact H].
Qed.

(** ** Class equality (for the fuel context encoding) *)

Definition fc_eqb (a b : fclass) : bool :=
  match a, b with F0,F0 | F1,F1 | F2,F2 => true | _,_ => false end.

Lemma fc_eqb_spec : forall a b, fc_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

(** A [positive] tag for each class, for building injective context
    encodings in the fuel instance. *)
Definition fc_tag (fc : fclass) : positive :=
  match fc with F0 => 1 | F1 => 2 | F2 => 3 end%positive.

Lemma fc_tag_inj : forall a b, fc_tag a = fc_tag b -> a = b.
Proof. intros [] [] H; simpl in H; congruence. Qed.
