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

(* --- counters track: session A appendix ------------------------- *)

(** ** More repetition algebra (unit-width changes)

    The gray/double families cross a comb with one unit width and
    deposit another; these fold a repetition between unit sizes. *)

Lemma rep_dblu : forall (u : list Sym) k, rep (u ++ u) k = rep u (2 * k).
Proof.
  induction k; simpl.
  - reflexivity.
  - rewrite IHk.
    replace (k + S (k + 0)) with (S (2 * k)) by lia.
    simpl. rewrite app_assoc. reflexivity.
Qed.

Lemma rep_trip : forall (x : Sym) k, rep [x; x; x] k = rep [x] (3 * k).
Proof.
  induction k; simpl.
  - reflexivity.
  - rewrite IHk.
    replace (k + S (k + S (k + 0))) with (S (S (3 * k))) by lia.
    reflexivity.
Qed.

(** ** The Gray-code slot encoding (gray_counter family)

    #19 stores its counter as a GRAY code right of the comb: slot i
    (3 cells [bit; 0; 0], LSB first) holds bit i of G(p) = p xor
    (p >> 1), trimmed at the top marker.  Since bit i of G is
    (bit i of p) xor (bit i+1 of p), the encoding recurses with a
    one-bit lookahead ([oddb]).  The increment p -> p+1 flips exactly
    bit j of G where j = fst (cview p) -- the SAME carry view as the
    binary families -- and the decomposition lemmas below expose the
    flip slot for the interior and overflow shapes. *)

Definition oddb (p : positive) : bool :=
  match p with xO _ => false | _ => true end.

Fixpoint Wg (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => (if oddb q then S1 else S0) :: S0 :: S0 :: Wg q
  | xI q => (if oddb q then S0 else S1) :: S0 :: S0 :: Wg q
  end.

(** Definitional equations, kept as rewrite handles so the proofs
    below never [simpl] a stuck [Wg]. *)
Lemma Wg_xO : forall p,
  Wg (xO p) = (if oddb p then S1 else S0) :: S0 :: S0 :: Wg p.
Proof. reflexivity. Qed.

Lemma Wg_xI : forall p,
  Wg (xI p) = (if oddb p then S0 else S1) :: S0 :: S0 :: Wg p.
Proof. reflexivity. Qed.

Lemma succ_xI : forall p, Pos.succ (xI p) = xO (Pos.succ p).
Proof. reflexivity. Qed.

(** Interior carry: p = 1^(j+1) 0 q in low-bit order.  Slots 0..j-1
    are clear, slot j is the marker the head finds, slot j+1 is the
    flip (its pre/post values are the heads of [Wg (xO q)] /
    [Wg (xI q)]), and everything above is untouched. *)
Lemma Wg_some : forall p j q, cview p = (S j, Some q) ->
  Wg p = rep [S0; S0; S0] j ++ S1 :: S0 :: S0 :: Wg (xO q) /\
  Wg (Pos.succ p) = rep [S0; S0; S0] j ++ S1 :: S0 :: S0 :: Wg (xI q).
Proof.
  induction p as [p IHp | p IHp |]; intros j q H; simpl in H.
  - (* p' = xI p *)
    destruct (cview p) as [j' o] eqn:Er.
    injection H as Hj ->. subst j.
    destruct j' as [| j''].
    + (* the marker slot: p = xO q *)
      assert (p = xO q) as ->.
      { destruct p as [x|x|]; simpl in Er.
        - destruct (cview x); discriminate.
        - now injection Er as ->.
        - discriminate. }
      split; reflexivity.
    + (* below the marker: p = xI x *)
      destruct (IHp j'' q eq_refl) as (H1 & H2).
      assert (exists x, p = xI x) as (x & ->).
      { destruct p as [x|x|]; simpl in Er; eauto; discriminate. }
      split.
      * rewrite Wg_xI. cbn [oddb].
        rewrite H1. reflexivity.
      * rewrite !succ_xI. rewrite Wg_xO. cbn [oddb].
        rewrite succ_xI in H2.
        rewrite H2. reflexivity.
  - discriminate.
  - discriminate.
Qed.

(** Overflow: p = 2^(j+1) - 1, G(p) = 2^j.  The head finds the top
    marker at slot j and the flip EXTENDS the code: slot j stays set
    and a new top marker appears at slot j+1. *)
Lemma Wg_none : forall p j, cview p = (S j, None) ->
  Wg p = rep [S0; S0; S0] j ++ [S1] /\
  Wg (Pos.succ p) = rep [S0; S0; S0] j ++ [S1; S0; S0; S1].
Proof.
  induction p as [p IHp | p IHp |]; intros j H; simpl in H.
  - destruct (cview p) as [j' o] eqn:Er.
    injection H as Hj ->. subst j.
    destruct j' as [| j''].
    + (* cview p = (0, None) is impossible *)
      exfalso.
      destruct p as [x|x|]; simpl in Er.
      * destruct (cview x); discriminate.
      * discriminate.
      * discriminate.
    + destruct (IHp j'' eq_refl) as (H1 & H2).
      assert (p = xH \/ exists x, p = xI x) as [-> | (x & ->)].
      { destruct p as [x|x|]; simpl in Er; eauto. discriminate. }
      * simpl in Er. injection Er as <-.
        split; reflexivity.
      * split.
        -- rewrite Wg_xI. cbn [oddb].
           rewrite H1. reflexivity.
        -- rewrite !succ_xI. rewrite Wg_xO. cbn [oddb].
           rewrite succ_xI in H2.
           rewrite H2. reflexivity.
  - discriminate.
  - injection H as <-. split; reflexivity.
Qed.

(** ** Gray comb alignment (the (10)-comb, crossed two units at a
    time, and the flip-write refolds) *)

Lemma comb_even : forall c X,
  rep [S1; S0] (2 * c) ++ X = rep [S1; S0; S1; S0] c ++ X.
Proof.
  intros. rewrite <- rep_dblu. reflexivity.
Qed.

Lemma comb_odd : forall c X,
  rep [S1; S0] (2 * c + 1) ++ X
  = rep [S1; S0; S1; S0] c ++ S1 :: S0 :: X.
Proof.
  intros.
  rewrite rep_add, <- rep_dblu, <- app_assoc.
  reflexivity.
Qed.

(** After the return sweep, the deposited (01)-run refolds with the
    turnaround cells into the one-longer comb. *)
Lemma comb_refold : forall k X,
  S1 :: S0 :: S1 :: rep [S0; S1] k ++ S0 :: X
  = rep [S1; S0] (k + 2) ++ X.
Proof.
  intros k X. induction k as [| k IH].
  - reflexivity.
  - replace (S k + 2) with (S (k + 2)) by lia.
    cbn [rep app] in *.
    now rewrite IH.
Qed.

(** The crossing deposit read back as return-sweep units. *)
Lemma cross_ret : forall m X,
  rep [S0; S1; S0; S1] (S m) ++ X
  = S0 :: rep [S1; S0] (S (2 * m)) ++ S1 :: X.
Proof.
  intros m X. induction m as [| m IH].
  - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    cbn [rep app] in *.
    now rewrite IH.
Qed.

(** Variant absorbing the leading return cell (odd-comb laps). *)
Lemma cross_ret2 : forall m X,
  S1 :: rep [S0; S1; S0; S1] (S m) ++ X
  = rep [S1; S0] (S (S (2 * m))) ++ S1 :: X.
Proof.
  intros. rewrite cross_ret. reflexivity.
Qed.
