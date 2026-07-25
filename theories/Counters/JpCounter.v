(** * JpCounter: the complemented interleaved-counter encoding.

    Wave-8 support file for the interleaved-counter auto-emitter.  [Jp] is
    [ILCounter.Ip] with the data cell [S0]/[S1] swapped: the census's
    comb-free interleaved binary counters decode to a value that DESCENDS
    within each doubling block (the physical carry runs in the complement
    sense), so the anchor tape is [Jp p], and the whole ILCounter increment
    structure transfers through the three mirror decomposition lemmas below.

    Axiom footprint: [functional_extensionality_dep] only (the proofs are the
    ILCounter [Ip] proofs with the data bits flipped). *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter ILCounter.
Import ListNotations.

Fixpoint Jp (p : positive) : list Sym :=
  match p with xH => [S1] | xO q => S1 :: S1 :: Jp q | xI q => S1 :: S0 :: Jp q end.

Lemma Jp_head : forall p, exists w, Jp p = S1 :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma cview_some_J : forall p j q, cview p = (j, Some q) ->
  Jp p = rep [S1; S0] j ++ S1 :: S1 :: Jp q /\
  Jp (Pos.succ p) = rep [S1; S1] j ++ S1 :: S0 :: Jp q.
Proof. induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2). split; simpl; [rewrite H1|rewrite H2]; reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate. Qed.

Lemma cview_none_J : forall p j, cview p = (S j, None) ->
  Jp p = rep [S1; S0] j ++ [S1] /\ Jp (Pos.succ p) = rep [S1; S1] (S j) ++ [S1].
Proof. induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r. destruct j as [|j].
    + exfalso. destruct p; simpl in E; [destruct (cview p); discriminate|discriminate|discriminate].
    + destruct (IHp j eq_refl) as (H1 & H2). split; simpl; [rewrite H1|rewrite H2]; reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity. Qed.

Lemma pair_rot : forall (x y : Sym) j, rep [x;y] j ++ [x] = x :: rep [y;x] j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.

Fixpoint tovf (p : positive) : nat :=
  match p with xH => 0 | xO q => S (2 * tovf q) | xI q => 2 * tovf q end.

Lemma tovf_succ : forall p, tovf p <> 0 -> tovf (Pos.succ p) = Nat.pred (tovf p).
Proof. induction p; intro H; simpl in *; [rewrite IHp by lia; lia | lia | lia]. Qed.

Lemma tovf0_allones : forall p, tovf p = 0 -> exists j, cview p = (S j, None).
Proof. induction p; intro H; simpl in *.
  - assert (tovf p = 0) by lia. destruct (IHp H0) as (j & Hj). rewrite Hj. exists (S j); reflexivity.
  - lia. - exists 0; reflexivity. Qed.
