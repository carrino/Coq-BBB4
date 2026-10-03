(** * Counters.LoopMirrorTr: one counter held on both sides of the head
    (SCOPING_INSTR 7.4.LE10).

    In LE7's mirror rows and several of LE8's leftovers, the head works at
    a JUNCTION between two digit strings, one growing leftwards and one
    rightwards, with both LSBs at the junction.  Every increment is two
    one-sided arms: the right carry leaves the anchor [mk1] and ends at a
    second junction configuration [mk2]; the left carry goes from [mk2]
    back to [mk1].  The two sides hold the same count up to a fixed offset
    [a] (left = [n + a], right = [n]) and may have different widths.

    The state is indexed by one number [n].  [nb m n] is the [m]-bit
    expansion of [n], LSB first, and [nb_succ] says it is [binc] below
    [2^m].  So [mirror_iter] runs every increment from [n] to [n + d] by
    induction on [d].  The arms are row-specific hypotheses about any
    carry length and any far context.

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr.
Import ListNotations.

Fixpoint nb (m n : nat) : list bool :=
  match m with
  | O => []
  | S m' => Nat.odd n :: nb m' (Nat.div2 n)
  end.

Lemma nb_length : forall m n, length (nb m n) = m.
Proof. induction m as [|m IH]; intros n; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pow2_S : forall m, 2 ^ S m = 2 * 2 ^ m.
Proof. intros m. reflexivity. Qed.

Lemma odd_double : forall k, Nat.odd (2 * k) = false.
Proof. intros k. rewrite Nat.odd_mul. reflexivity. Qed.

Lemma odd_succ_double : forall k, Nat.odd (S (2 * k)) = true.
Proof. intros k. rewrite Nat.odd_succ, Nat.even_mul. reflexivity. Qed.

Lemma odd_dp1 : forall k, Nat.odd (2 * k + 1) = true.
Proof. intros k. rewrite Nat.add_1_r. apply odd_succ_double. Qed.

Lemma nb_succ : forall m n, S n < 2 ^ m -> nb m (S n) = binc (nb m n).
Proof.
  induction m as [|m IH]; intros n Hn; [cbn in Hn; lia|].
  cbn [nb]. destruct (Nat.Even_or_Odd n) as [[k ->]|[k ->]].
  - rewrite odd_succ_double, odd_double.
    replace (Nat.div2 (S (2 * k))) with k by (symmetry; apply Nat.div2_succ_double).
    replace (Nat.div2 (2 * k)) with k by (symmetry; apply Nat.div2_double).
    reflexivity.
  - replace (S (2 * k + 1)) with (2 * S k) by lia. rewrite odd_double, odd_dp1.
    replace (Nat.div2 (2 * S k)) with (S k) by (symmetry; apply Nat.div2_double).
    replace (Nat.div2 (2 * k + 1)) with k
      by (replace (2 * k + 1) with (S (2 * k)) by lia; symmetry; apply Nat.div2_succ_double).
    cbn [binc]. f_equal. apply IH. rewrite pow2_S in Hn. lia.
Qed.

Lemma nb_split : forall m n, S n < 2 ^ m -> exists k r, nb m n = repeat true k ++ false :: r.
Proof.
  induction m as [|m IH]; intros n Hn; [cbn in Hn; lia|].
  cbn [nb]. destruct (Nat.Even_or_Odd n) as [[j ->]|[j ->]].
  - exists 0, (nb m (Nat.div2 (2 * j))). rewrite odd_double. reflexivity.
  - rewrite odd_dp1.
    replace (Nat.div2 (2 * j + 1)) with j
      by (replace (2 * j + 1) with (S (2 * j)) by lia; symmetry; apply Nat.div2_succ_double).
    destruct (IH j) as (k & r & E); [rewrite pow2_S in Hn; lia|].
    exists (S k), r. rewrite E. reflexivity.
Qed.

Lemma nb_zero : forall m, nb m 0 = repeat false m.
Proof. induction m as [|m IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma nb_full : forall m, nb m (2 ^ m - 1) = repeat true m.
Proof.
  induction m as [|m IH]; [reflexivity|]. cbn [nb].
  pose proof (Nat.pow_nonzero 2 m ltac:(lia)) as H.
  replace (2 ^ S m - 1) with (2 * (2 ^ m - 1) + 1) by (rewrite pow2_S; lia).
  rewrite odd_dp1.
  replace (Nat.div2 (2 * (2 ^ m - 1) + 1)) with (2 ^ m - 1)
    by (replace (2 * (2 ^ m - 1) + 1) with (S (2 * (2 ^ m - 1))) by lia;
        symmetry; apply Nat.div2_succ_double).
  rewrite IH. reflexivity.
Qed.

Lemma bcells_f : forall Z O r, bcells Z O (false :: r) = Z ++ bcells Z O r.
Proof. reflexivity. Qed.

Lemma bcells_t : forall Z O r, bcells Z O (true :: r) = O ++ bcells Z O r.
Proof. reflexivity. Qed.

Lemma bcells_alltrue : forall Z O m, bcells Z O (repeat true m) = rep O m.
Proof. intros Z O m. induction m as [|m IH]; [reflexivity|]. cbn [repeat]. rewrite bcells_t, IH. reflexivity. Qed.

Lemma bcells_allfalse : forall Z O m, bcells Z O (repeat false m) = rep Z m.
Proof. intros Z O m. induction m as [|m IH]; [reflexivity|]. cbn [repeat]. rewrite bcells_f, IH. reflexivity. Qed.

Lemma nb_one : forall m, nb (S m) 1 = true :: repeat false m.
Proof. intros m. cbn [nb]. rewrite <- nb_zero. reflexivity. Qed.

Lemma nb_full_m1 : forall m, nb (S m) (2 ^ S m - 2) = false :: repeat true m.
Proof.
  intros m. pose proof (Nat.pow_nonzero 2 m ltac:(lia)) as H.
  replace (2 ^ S m - 2) with (2 * (2 ^ m - 1)) by (rewrite pow2_S; lia).
  cbn [nb]. rewrite odd_double, Nat.div2_double, nb_full. reflexivity.
Qed.

Section Mirror.
Variable tm : TM.
Variables mk1 mk2 : list Sym -> list Sym -> cconf.
Variables ZL OL ZR OR : list Sym.

Hypothesis HR : forall k r Lc R',
  Reach0 tm (mk1 Lc (bcells ZR OR (repeat true k ++ false :: r) ++ R'))
            (mk2 Lc (bcells ZR OR (repeat false k ++ true :: r) ++ R')).
Hypothesis HL : forall k r L' Rc,
  Reach0 tm (mk2 (bcells ZL OL (repeat true k ++ false :: r) ++ L') Rc)
            (mk1 (bcells ZL OL (repeat false k ++ true :: r) ++ L') Rc).

Lemma mirror_inc : forall x y L' R',
  (exists k r, x = repeat true k ++ false :: r) ->
  (exists k r, y = repeat true k ++ false :: r) ->
  Reach0 tm (mk1 (bcells ZL OL x ++ L') (bcells ZR OR y ++ R'))
            (mk1 (bcells ZL OL (binc x) ++ L') (bcells ZR OR (binc y) ++ R')).
Proof.
  intros x y L' R' (kx & rx & ->) (ky & ry & ->). rewrite !binc_int.
  eapply reach0_trans; [apply HR|]. apply HL.
Qed.

Variables mL mR a : nat.
Variables L' R' : list Sym.

Definition mconf (n : nat) : cconf :=
  mk1 (bcells ZL OL (nb mL (n + a)) ++ L') (bcells ZR OR (nb mR n) ++ R').

Lemma mirror_iter : forall d n, n + d + a < 2 ^ mL -> n + d < 2 ^ mR ->
  Reach0 tm (mconf n) (mconf (n + d)).
Proof.
  induction d as [|d IH]; intros n HL' HR'.
  - rewrite Nat.add_0_r. apply reach0_refl.
  - eapply reach0_trans; [|replace (n + S d) with (S n + d) by lia; apply IH; lia].
    unfold mconf. cbn [Nat.add]. rewrite (nb_succ mL (n + a)) by lia. rewrite (nb_succ mR n) by lia.
    apply mirror_inc; apply nb_split; lia.
Qed.
End Mirror.
