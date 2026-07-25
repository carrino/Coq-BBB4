(** * IXPGadgets: positive gadgets bridging the two counter levels of an
    exponential-overflow (IXP) interleaved counter.

    Shared by the IXP_*/IXPM_* boards (first instance: the hand-authored
    IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD, which carries its own private copies).
    The overflow lap 2^K-1 -> 2^K of an IXP machine runs an INNER interleaved
    counter from 2^(K-1) up to the all-ones fill 2^K-1; these gadgets tie the
    outer [cview] overflow shape to the inner boot value [pow2] and the inner
    termination value [fill]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter ILCounter JpCounter.
Import ListNotations.

Fixpoint pow2 (n : nat) : positive :=
  match n with O => xH | S m => xO (pow2 m) end.

(** All-ones of the same width. *)
Fixpoint fill (v : positive) : positive :=
  match v with xH => xH | xO q => xI (fill q) | xI q => xI (fill q) end.

Lemma Ip_pow2 : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma fill_succ : forall v j q, cview v = (j, Some q) ->
  fill (Pos.succ v) = fill v.
Proof.
  induction v; intros j q H; simpl in H.
  - destruct (cview v) as [j' r] eqn:E. inversion H; subst.
    simpl. f_equal. exact (IHv _ _ eq_refl).
  - inversion H; subst. reflexivity.
  - discriminate.
Qed.

Lemma fill_allones : forall v j, cview v = (S j, None) -> fill v = v.
Proof.
  induction v; intros j H; simpl in H.
  - destruct (cview v) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    { exfalso. destruct v; simpl in E; [destruct (cview v); discriminate|discriminate|discriminate]. }
    simpl. f_equal. exact (IHv j eq_refl).
  - discriminate.
  - reflexivity.
Qed.

Lemma cview_none_shape : forall p j, cview p = (S j, None) ->
  p = fill (pow2 j).
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    { exfalso. destruct p; simpl in E; [destruct (cview p); discriminate|discriminate|discriminate]. }
    simpl. f_equal. exact (IHp j eq_refl).
  - discriminate.
  - inversion H; subst. reflexivity.
Qed.
