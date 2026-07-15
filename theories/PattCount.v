(** * PattCount: occurrence counting of symbol patterns in lists.

    The list-combinatorics substrate of the n-gram *pattern measures*
    (the full measure vocabulary of the C verifier's [rkv_delta],
    src/verify.c): [occ p xs] counts the positions of [xs] where the
    word [p] occurs (as a contiguous infix starting at that position
    and fitting inside [xs]).

    The lemmas quantify how [occ] changes under the edits a TM step
    performs on the padded tape text:

    - [occ_update]: rewriting one interior cell changes the count by
      the count difference over the fixed [2|p|-1]-cell window around
      that cell (everything else cancels) -- the heart of the
      whole-tape ('A'-region) measure delta;
    - the definitional cons unfolding (a cell pushed at the head of a
      half-tape adds exactly the prefix-occurrence indicator) -- the
      L/R-region deltas;
    - [occ_cons_blank] / [occ_app_blank]: a blank added beyond a
      blank margin of width [|p|-1] changes nothing (for patterns
      containing a nonblank), which absorbs the list/function
      half-tape mismatch when a step walks off the written region. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

(** ** Small list utilities *)

Lemma pc_repeat_shift : forall (x : Sym) k,
  x :: repeat x k = repeat x k ++ [x].
Proof. induction k; simpl; congruence. Qed.

Lemma pad_rotate : forall (x : Sym) k (Y : list Sym),
  repeat x k ++ x :: Y = x :: repeat x k ++ Y.
Proof. induction k; intros Y; simpl; congruence. Qed.

Lemma pc_rev_repeat : forall (x : Sym) k, rev (repeat x k) = repeat x k.
Proof.
  induction k; simpl; [reflexivity|].
  rewrite IHk, <- pc_repeat_shift. reflexivity.
Qed.

Lemma firstn_S_pred : forall (x : Sym) z k,
  1 <= k -> firstn k (x :: z) = x :: firstn (k - 1) z.
Proof.
  intros x z k H. destruct k; [lia|].
  simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma firstn_pad_app : forall k (X : list Sym),
  firstn k (repeat S0 k ++ X) = repeat S0 k.
Proof.
  intros k X.
  rewrite firstn_app, repeat_length, Nat.sub_diag.
  simpl. rewrite app_nil_r.
  apply firstn_all2. rewrite repeat_length. lia.
Qed.

(** ** Boolean word equality *)

Fixpoint syms_eqb (a b : list Sym) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => sym_eqb x y && syms_eqb a' b'
  | _, _ => false
  end.

Lemma syms_eqb_eq : forall a b, syms_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a' IH]; destruct b as [|y b']; simpl; split;
    intro H; try congruence.
  - apply andb_prop in H as [H1 H2].
    apply sym_eqb_spec in H1. apply IH in H2. congruence.
  - injection H as H1 H2. subst.
    apply andb_true_intro. split.
    + apply sym_eqb_spec. reflexivity.
    + apply IH. reflexivity.
Qed.

(** ** Occurrences *)

(** [p] occurs at the head of [xs] (entirely: a tail of [xs] shorter
    than [p] does not count). *)
Definition prefix_eqb (p xs : list Sym) : bool :=
  syms_eqb p (firstn (length p) xs).

Fixpoint occ (p xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | _ :: t => (if prefix_eqb p xs then 1 else 0) + occ p t
  end.

Lemma occ_cons : forall p x t,
  occ p (x :: t) = (if prefix_eqb p (x :: t) then 1 else 0) + occ p t.
Proof. reflexivity. Qed.

(** ** [firstn] toolkit *)

Lemma pc_firstn_repeat : forall (x : Sym) k m,
  firstn k (repeat x m) = repeat x (Nat.min k m).
Proof.
  induction k; intros [|m]; simpl; try reflexivity.
  rewrite IHk. reflexivity.
Qed.

(** A prefix probe never reaches past a long enough carrier. *)
Lemma prefix_eqb_app_l : forall p u v,
  length p <= length u ->
  prefix_eqb p (u ++ v) = prefix_eqb p u.
Proof.
  intros p u v H. unfold prefix_eqb.
  rewrite firstn_app.
  replace (length p - length u) with 0 by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Beyond a nonempty carrier, a prefix probe reaches at most
    [|p| - 1] cells into the continuation. *)
Lemma prefix_eqb_trunc : forall p u v,
  1 <= length u ->
  prefix_eqb p (u ++ firstn (length p - 1) v) = prefix_eqb p (u ++ v).
Proof.
  intros p u v H. unfold prefix_eqb.
  rewrite !firstn_app, firstn_firstn.
  replace (Nat.min (length p - length u) (length p - 1))
    with (length p - length u) by lia.
  reflexivity.
Qed.

Lemma prefix_eqb_trunc_cons : forall p x u v,
  prefix_eqb p (x :: u ++ firstn (length p - 1) v)
  = prefix_eqb p (x :: u ++ v).
Proof.
  intros. apply (prefix_eqb_trunc p (x :: u) v). simpl; lia.
Qed.

(** ** Bounded occurrence sums (positions inside a prefix) *)

Fixpoint occ_bnd (p u v : list Sym) : nat :=
  match u with
  | [] => 0
  | _ :: u' => (if prefix_eqb p (u ++ v) then 1 else 0) + occ_bnd p u' v
  end.

Lemma occ_app : forall p u v,
  occ p (u ++ v) = occ_bnd p u v + occ p v.
Proof.
  induction u as [|x u' IH]; intro v; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma occ_bnd_trunc : forall p u v,
  occ_bnd p u v = occ_bnd p u (firstn (length p - 1) v).
Proof.
  induction u as [|x u' IH]; intro v; simpl.
  - reflexivity.
  - rewrite prefix_eqb_trunc_cons, IH. reflexivity.
Qed.

(** ** Single-cell update: only the surrounding window matters *)

Lemma occ_split_c : forall p mid c post,
  occ p (mid ++ c :: post)
  = occ_bnd p (mid ++ [c]) (firstn (length p - 1) post) + occ p post.
Proof.
  intros. rewrite <- occ_bnd_trunc.
  replace (mid ++ c :: post) with ((mid ++ [c]) ++ post)
    by (rewrite <- app_assoc; reflexivity).
  apply occ_app.
Qed.

Lemma occ_wnd : forall p mid c post,
  occ p (mid ++ c :: firstn (length p - 1) post)
  = occ_bnd p (mid ++ [c]) (firstn (length p - 1) post)
    + occ p (firstn (length p - 1) post).
Proof.
  intros.
  rewrite (occ_split_c p mid c (firstn (length p - 1) post)).
  rewrite firstn_firstn, Nat.min_id.
  reflexivity.
Qed.

(** Rewriting cell [c] at depth [>= |p| - 1] into the text: the count
    change equals the change over the window [mid ++ c :: firstn
    (|p|-1) post] (stated additively to stay in [nat]). *)
Lemma occ_update : forall p pre0 mid x y post,
  length p - 1 <= length mid ->
  occ p (pre0 ++ mid ++ x :: post)
    + occ p (mid ++ y :: firstn (length p - 1) post)
  = occ p (pre0 ++ mid ++ y :: post)
    + occ p (mid ++ x :: firstn (length p - 1) post).
Proof.
  intros p pre0 mid x y post Hm.
  induction pre0 as [|a pre0' IH]; simpl app.
  - rewrite !occ_wnd, !occ_split_c. lia.
  - rewrite !occ_cons.
    replace (a :: pre0' ++ mid ++ x :: post)
      with ((a :: pre0' ++ mid) ++ x :: post)
      by (simpl; rewrite <- app_assoc; reflexivity).
    replace (a :: pre0' ++ mid ++ y :: post)
      with ((a :: pre0' ++ mid) ++ y :: post)
      by (simpl; rewrite <- app_assoc; reflexivity).
    rewrite !(prefix_eqb_app_l p (a :: pre0' ++ mid))
      by (simpl; rewrite app_length; lia).
    lia.
Qed.

(** ** Blank absorption *)

Lemma syms_eqb_repeat_S0 : forall p k,
  In S1 p -> syms_eqb p (repeat S0 k) = false.
Proof.
  intros p k H1.
  destruct (syms_eqb p (repeat S0 k)) eqn:E; [|reflexivity].
  apply syms_eqb_eq in E. subst p.
  apply repeat_spec in H1. discriminate.
Qed.

Lemma prefix_eqb_repeat_S0 : forall p m,
  In S1 p -> prefix_eqb p (repeat S0 m) = false.
Proof.
  intros p m H1. unfold prefix_eqb.
  rewrite pc_firstn_repeat.
  apply syms_eqb_repeat_S0. assumption.
Qed.

Lemma occ_repeat_S0 : forall p m, In S1 p -> occ p (repeat S0 m) = 0.
Proof.
  intros p m H1. induction m as [|m IH]; simpl.
  - reflexivity.
  - change (S0 :: repeat S0 m) with (repeat S0 (S m)).
    rewrite prefix_eqb_repeat_S0 by assumption.
    apply IH.
Qed.

(** A blank pushed onto a blank-margined text adds no occurrence. *)
Lemma occ_cons_blank : forall p z,
  In S1 p ->
  firstn (length p - 1) z = repeat S0 (length p - 1) ->
  occ p (S0 :: z) = occ p z.
Proof.
  intros p z H1 Hz.
  destruct p as [|s p']; [destruct H1|].
  rewrite occ_cons.
  unfold prefix_eqb.
  cbn [length firstn].
  simpl in Hz. rewrite Nat.sub_0_r in Hz. rewrite Hz.
  change (S0 :: repeat S0 (length p')) with (repeat S0 (S (length p'))).
  rewrite syms_eqb_repeat_S0 by assumption.
  reflexivity.
Qed.

(** A blank appended beyond a blank margin adds no occurrence. *)
Lemma occ_app_blank : forall p y,
  In S1 p ->
  occ p (y ++ repeat S0 (length p - 1) ++ [S0])
  = occ p (y ++ repeat S0 (length p - 1)).
Proof.
  intros p y H1.
  induction y as [|a y' IH]; simpl app.
  - change [S0] with (repeat S0 1).
    rewrite <- repeat_app.
    rewrite !occ_repeat_S0 by assumption.
    reflexivity.
  - rewrite !occ_cons.
    replace (a :: y' ++ repeat S0 (length p - 1) ++ [S0])
      with ((a :: y' ++ repeat S0 (length p - 1)) ++ [S0])
      by (simpl; rewrite <- app_assoc; reflexivity).
    rewrite (prefix_eqb_app_l p (a :: y' ++ repeat S0 (length p - 1)))
      by (simpl; rewrite app_length, repeat_length; lia).
    rewrite IH. reflexivity.
Qed.
