(** * BinVal: a half-tape read as a binary number, plus the [last] / [rep]
    algebra the macro-rule proofs of [docs/WAVE36_MXDYS_FOUR.md] need.

    A half-tape list is nearest-cell-first, so reading it as a binary
    number with the NEAREST cell least significant is the natural
    numeration:

      bval [] = 0        bval (b :: t) = sval b + 2 * bval t

    The two facts that carry the weight are [bval_lt] (a list of length
    [n] denotes a number below [2^n], which is what bounds the measure)
    and [bval_rep0_app] (a run of blanks in front of a list scales its
    value by [2^k], which is what makes the per-rule deltas exact).

    No axioms of its own. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** Parity, in the shape [lia] can consume directly *)

Definition OddN (n : nat) : Prop := exists j, n = S (2 * j).
Definition EvenN (n : nat) : Prop := exists j, n = 2 * j.

(** Stated as two implications, not an [iff]: [apply _ in H] on an [iff]
    whose two sides both unify picks a direction by luck. *)
Lemma oddN_SS_inv : forall n, OddN (S (S n)) -> OddN n.
Proof. intros n [j Hj]; exists (j - 1); lia. Qed.

Lemma oddN_SS_intro : forall n, OddN n -> OddN (S (S n)).
Proof. intros n [j Hj]; exists (S j); lia. Qed.

Lemma evenN_SS_inv : forall n, EvenN (S (S n)) -> EvenN n.
Proof. intros n [j Hj]; exists (j - 1); lia. Qed.

Lemma evenN_SS_intro : forall n, EvenN n -> EvenN (S (S n)).
Proof. intros n [j Hj]; exists (S j); lia. Qed.

Lemma oddN_0 : ~ OddN 0.
Proof. intros [j Hj]; lia. Qed.

Lemma evenN_1 : ~ EvenN 1.
Proof. intros [j Hj]; lia. Qed.

Lemma oddN_1 : OddN 1.
Proof. exists 0; reflexivity. Qed.

Lemma evenN_0 : EvenN 0.
Proof. exists 0; reflexivity. Qed.

(** ** The numeration *)

Definition sval (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Fixpoint bval (l : list Sym) : nat :=
  match l with
  | [] => 0
  | b :: t => sval b + 2 * bval t
  end.

Lemma sval_le : forall s, sval s <= 1.
Proof. destruct s; simpl; lia. Qed.

Lemma bval_lt : forall l, bval l < 2 ^ length l.
Proof.
  induction l as [|b t IH]; simpl; [lia|].
  pose proof (sval_le b). lia.
Qed.

Lemma bval_rep0_app : forall k m, bval (rep [S0] k ++ m) = 2 ^ k * bval m.
Proof.
  induction k as [|k IH]; intro m; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma length_rep1 : forall (x : Sym) k, length (rep [x] k) = k.
Proof.
  induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma rep_S : forall (x : Sym) k, rep [x] (S k) = x :: rep [x] k.
Proof. reflexivity. Qed.

(** ** [last], the far end of a half-tape *)

Lemma last_cons_ne : forall (a : Sym) l d, l <> [] -> last (a :: l) d = last l d.
Proof. intros a [|y l] d H; [contradiction | reflexivity]. Qed.

Lemma last_app_cons : forall (l m : list Sym) a d,
  last (l ++ a :: m) d = last (a :: m) d.
Proof.
  induction l as [|x l IH]; intros m a d; [reflexivity|].
  cbn [app].
  rewrite last_cons_ne by (destruct l; cbn [app]; discriminate).
  apply IH.
Qed.

Lemma last_nonnil : forall l, last l S0 = S1 -> l <> [].
Proof. intros [|x l] H; [discriminate | discriminate]. Qed.

Lemma chd_rep0_app : forall k m, chd (rep [S0] (S k) ++ m) = S0.
Proof. reflexivity. Qed.
