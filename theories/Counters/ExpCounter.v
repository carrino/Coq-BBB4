(** * ExpCounter: stride-3 marker encodings (exp_counter family).

    The three exp_counter machines (#2, #4, #12 -- BBB certs
    counter2/4/12) carry a binary counter as stride-3 MARKERS: bit b
    of the value v sits alone in a 3-cell group, the other two cells
    blank.  Reading outward from the anchor the groups appear either
    zeros-first ([Tp], marker last in its group -- the #2 marker side
    and the #12 right side) or marker-first ([Gp] -- the #4 marker
    side and the #12 left side, which consume a 2-cell stub before
    the groups align).  The bit side of #2/#4 reuses MonoCounter's
    odd-cell [Wp].

    Same carry view [cview]; the decomposition lemmas produce the
    exact shapes the phase scripts consume: the set-marker groups as
    a [rep] block for the stride cycles, and the successor's cleared
    run as a flat [rep [S0]] block (the zeroing runs deposit plain
    blank cells). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** Zeros-first groups: bit b of [p] at the last cell of group b. *)
Fixpoint Tp (p : positive) : list Sym :=
  match p with
  | xH => [S0; S0; S1]
  | xO q => S0 :: S0 :: S0 :: Tp q
  | xI q => S0 :: S0 :: S1 :: Tp q
  end.

(** Marker-first groups: [Tp p = S0 :: S0 :: Gp p]. *)
Fixpoint Gp (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => S0 :: S0 :: S0 :: Gp q
  | xI q => S1 :: S0 :: S0 :: Gp q
  end.

Lemma Tp_head : forall p, exists w, Tp p = S0 :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma cview_some_T : forall p j q, cview p = (j, Some q) ->
  Tp p = rep [S0; S0; S1] j ++ S0 :: S0 :: S0 :: Tp q /\
  Tp (Pos.succ p) = rep [S0] (3 * j) ++ S0 :: S0 :: S1 :: Tp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split.
    + simpl. rewrite H1. reflexivity.
    + replace (3 * S j') with (S (S (S (3 * j')))) by lia.
      cbn [Pos.succ Tp rep app].
      rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_T : forall p j, cview p = (j, None) ->
  Tp p = rep [S0; S0; S1] j /\
  Tp (Pos.succ p) = rep [S0] (3 * j) ++ [S0; S0; S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' eq_refl) as (H1 & H2).
    split.
    + simpl. rewrite H1. reflexivity.
    + replace (3 * S j') with (S (S (S (3 * j')))) by lia.
      cbn [Pos.succ Tp rep app].
      rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

Lemma cview_some_G : forall p j q, cview p = (j, Some q) ->
  Gp p = rep [S1; S0; S0] j ++ S0 :: S0 :: S0 :: Gp q /\
  Gp (Pos.succ p) = rep [S0] (3 * j) ++ S1 :: S0 :: S0 :: Gp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split.
    + simpl. rewrite H1. reflexivity.
    + replace (3 * S j') with (S (S (S (3 * j')))) by lia.
      cbn [Pos.succ Gp rep app].
      rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_G : forall p j, cview p = (S j, None) ->
  Gp p = rep [S1; S0; S0] j ++ [S1] /\
  Gp (Pos.succ p) = rep [S0] (3 * S j) ++ [S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j' r.
    destruct j as [|j].
    { exfalso. destruct p; simpl in E;
        [destruct (cview p); discriminate | discriminate | discriminate]. }
    destruct (IHp j eq_refl) as (H1 & H2).
    split.
    + simpl. rewrite H1. reflexivity.
    + replace (3 * S (S j)) with (S (S (S (3 * S j)))) by lia.
      cbn [Pos.succ Gp rep app].
      rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** ** Run-length folds for the zeroing sweeps *)

(** A lone repeated cell fuses onto its run (rep_slide restated). *)
Lemma rep1_fold : forall (x : Sym) k X,
  rep [x] k ++ x :: X = rep [x] (S k) ++ X.
Proof.
  intros. cbn [rep app]. rewrite rep_slide. reflexivity.
Qed.

(** Doubled cells followed by a lone cell make an odd run. *)
Lemma ones_fold_S : forall (x : Sym) j X,
  rep [x; x] j ++ x :: X = rep [x] (S (2 * j)) ++ X.
Proof.
  intros. rewrite rep_dbl, rep1_fold. reflexivity.
Qed.

(** Tripled cells flatten to a run (the stride trails). *)
Lemma rep_tpl : forall (x : Sym) k, rep [x; x; x] k = rep [x] (3 * k).
Proof.
  induction k; simpl.
  - reflexivity.
  - rewrite IHk.
    replace (k + S (k + S (k + 0))) with (S (S (3 * k))) by lia.
    reflexivity.
Qed.
