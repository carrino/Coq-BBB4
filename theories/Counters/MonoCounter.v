(** * MonoCounter: shared structure of the 110-comb mono_counter family.

    The three mono_counter machines (#10, #26, #31 -- BBB certs
    counter10/26/31) share the anchor shape C(a) = (110)^a W(a) and
    the same three-sweep lap geometry; they differ in the edge state,
    the head offset at the anchor, and the transition tables driving
    the (identically shaped) unit runs.  This file carries what is
    machine-independent:

    - the working area [Wp] over [positive] (binary at odd cells,
      LSB first) and the carry view [cview] with its two
      decomposition lemmas (interior carry / overflow);
    - the comb alignment rewrites over [rep] (unit rotations, the
      carry-block fusions, the walk-back zero algebra);
    - the final working-area equations closing the two lap shapes. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** Working area and carry view *)

(** [a] in binary at odd cells, LSB first ([xI] = low bit 1).  Every
    [Wp] starts with the even pad cell [S0]. *)
Fixpoint Wp (p : positive) : list Sym :=
  match p with
  | xH => [S0; S1]
  | xO q => S0 :: S0 :: Wp q
  | xI q => S0 :: S1 :: Wp q
  end.

(** Carry view: number of low set bits, and what is above them
    ([None] iff p = 2^j - 1, the overflow shape). *)
Fixpoint cview (p : positive) : nat * option positive :=
  match p with
  | xH => (1, None)
  | xO q => (0, Some q)
  | xI q => let '(j, r) := cview q in (S j, r)
  end.

Lemma Wp_head : forall p, exists w, Wp p = S0 :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma cview_some_W : forall p j q, cview p = (j, Some q) ->
  Wp p = rep [S0; S1] j ++ S0 :: S0 :: Wp q /\
  Wp (Pos.succ p) = rep [S0; S0] j ++ S0 :: S1 :: Wp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_W : forall p j, cview p = (j, None) ->
  Wp p = rep [S0; S1] j /\
  Wp (Pos.succ p) = rep [S0; S0] j ++ [S0; S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** ** Comb alignment rewrites *)

(** A crossed comb boundary rotates: 10 (110)^k X = (101)^k 10 X. *)
Lemma rot_cross : forall k X,
  S1 :: S0 :: rep [S1; S1; S0] k ++ X
  = rep [S1; S0; S1] k ++ S1 :: S0 :: X.
Proof.
  induction k; intros; cbn [rep app].
  - reflexivity.
  - now rewrite IHk.
Qed.

(** After the carry stop, the pushed 1 fuses with the carry blocks
    and the comb top into walk-back blocks over the rotated comb. *)
Lemma alignS2 : forall j k,
  S1 :: rep [S1; S1] j ++ rep [S1; S1; S0] (S k) ++ [S1]
  = rep [S1; S1] (S j) ++ rep [S1; S0; S1] k ++ [S1; S0; S1].
Proof.
  intros.
  rewrite !rep_dbl.
  replace (2 * S j) with (S (S (2 * j))) by lia.
  cbn [rep app].
  rewrite !rep_slide.
  rewrite rot_cross.
  reflexivity.
Qed.

(** The zapped pairs expose a single leading zero cell. *)
Lemma align00 : forall j X,
  rep [S0; S0] (S j) ++ X = S0 :: rep [S0] (S (2 * j)) ++ X.
Proof.
  intros; cbn [rep app].
  now rewrite rep_dbl.
Qed.

(** The comb top after sweep 3 re-rotates for the final descent. *)
Lemma alignL3 : forall k,
  rep [S1; S1; S0] (S k) ++ [S1]
  = S1 :: rep [S1; S0; S1] k ++ [S1; S0; S1].
Proof.
  intros; cbn [rep app].
  now rewrite rot_cross.
Qed.

(** ** Final working areas of the two lap shapes *)

Lemma final_r_int : forall m j wq,
  S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
    S1 :: S0 :: (rep [S0] (S (2 * j)) ++ S1 :: S0 :: wq))
  = rep [S1; S0; S1] (S (S m)) ++
    S1 :: S0 :: (rep [S0; S0] j ++ S0 :: S1 :: S0 :: wq).
Proof.
  intros; cbn [rep app].
  rewrite rep_dbl, rep_slide.
  reflexivity.
Qed.

Lemma final_r_ov : forall m j,
  S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
    S1 :: S0 :: (rep [S0] (S (2 * j)) ++ [S1; S0]))
  = (rep [S1; S0; S1] (S (S m)) ++
     S1 :: S0 :: (rep [S0; S0] j ++ [S0; S1])) ++ [S0].
Proof.
  intros; cbn [rep app].
  rewrite rep_dbl, <- !app_assoc.
  cbn [app].
  rewrite rep_slide, <- !app_assoc.
  cbn [app].
  reflexivity.
Qed.

(** ** The contiguous binary encoding (spacer_counter family)

    The spacer counters keep the counter as plain binary -- one cell
    per bit, LSB nearest the working side -- instead of the odd-cell
    encoding [Wp].  Same [cview], new decomposition lemmas. *)

Fixpoint Bp (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => S0 :: Bp q
  | xI q => S1 :: Bp q
  end.

Lemma cview_some_B : forall p j q, cview p = (j, Some q) ->
  Bp p = rep [S1] j ++ S0 :: Bp q /\
  Bp (Pos.succ p) = rep [S0] j ++ S1 :: Bp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_B : forall p j, cview p = (j, None) ->
  Bp p = rep [S1] j /\
  Bp (Pos.succ p) = rep [S0] j ++ [S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.
