(** * Bigfoot: the BB(3,3) Cryptid 1RB2RA1LC_2LC1RB2RB_---2LA1LA.

    Following the BusyBeaverWiki page "Bigfoot" (S. Ligocki's rules,
    with the exact step counts and the proof skeleton given there), we
    prove the Collatz-like rules for the configurations

      A'(a, b, c) = 0^inf (12)^a 1^b <A 1^c 0^inf        (b, c even)
      A (a, b, c) = A'(a, 2b, 2c)

    with exact step counts, as kernel-checked facts about [csteps].
    The trajectory from the blank tape then follows in [BigfootRun]. *)

From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement CTape.
From BB33 Require Import Lib.
Import ListNotations.

(** ** The machine: 1RB2RA1LC_2LC1RB2RB_---2LA1LA *)

Definition bigfoot : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S2 DR StA)
  | StA, S2 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S2 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StB, S2 => Some (mkTrans S2 DR StB)
  | StC, S0 => None
  | StC, S1 => Some (mkTrans S2 DL StA)
  | StC, S2 => Some (mkTrans S1 DL StA)
  end.

(** ** Single steps

    Each transition, stated on the head-on-left form ([cfgL]) and the
    head-on-right form ([cfgR]); the [N] variants read the implicit
    blank at the end of a half-tape.  All are definitional. *)

Lemma sA0N : forall l, csteps bigfoot 1 (cfgR StA l []) = Some (cfgR StB (S1 :: l) []).
Proof. reflexivity. Qed.
Lemma sA0NL : forall r, csteps bigfoot 1 (cfgL StA [] r) = Some (cfgR StB [S1] r).
Proof. reflexivity. Qed.
Lemma sA1L : forall l r, csteps bigfoot 1 (cfgL StA (S1 :: l) r) = Some (cfgR StA (S2 :: l) r).
Proof. reflexivity. Qed.
Lemma sA1R : forall l r, csteps bigfoot 1 (cfgR StA l (S1 :: r)) = Some (cfgR StA (S2 :: l) r).
Proof. reflexivity. Qed.
Lemma sA2L : forall l r, csteps bigfoot 1 (cfgL StA (S2 :: l) r) = Some (cfgL StC l (S1 :: r)).
Proof. reflexivity. Qed.
Lemma sA2R : forall l r, csteps bigfoot 1 (cfgR StA l (S2 :: r)) = Some (cfgL StC l (S1 :: r)).
Proof. reflexivity. Qed.
Lemma sB0N : forall l, csteps bigfoot 1 (cfgR StB l []) = Some (cfgL StC l [S2]).
Proof. reflexivity. Qed.
Lemma sB1R : forall l r, csteps bigfoot 1 (cfgR StB l (S1 :: r)) = Some (cfgR StB (S1 :: l) r).
Proof. reflexivity. Qed.
Lemma sB2R : forall l r, csteps bigfoot 1 (cfgR StB l (S2 :: r)) = Some (cfgR StB (S2 :: l) r).
Proof. reflexivity. Qed.
Lemma sC1L : forall l r, csteps bigfoot 1 (cfgL StC (S1 :: l) r) = Some (cfgL StA l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma sC1R : forall l r, csteps bigfoot 1 (cfgR StC l (S1 :: r)) = Some (cfgL StA l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma sC2L : forall l r, csteps bigfoot 1 (cfgL StC (S2 :: l) r) = Some (cfgL StA l (S1 :: r)).
Proof. reflexivity. Qed.
Lemma sC2R : forall l r, csteps bigfoot 1 (cfgR StC l (S2 :: r)) = Some (cfgL StA l (S1 :: r)).
Proof. reflexivity. Qed.

(** ** Shift rules (chain steps) *)

(** [A> 1^n  ->  2^n A>] *)
Lemma chain_A1 : forall n l r,
  csteps bigfoot n (cfgR StA l (repeat S1 n ++ r)) = Some (cfgR StA (repeat S2 n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StA (S2 :: l) (repeat S1 n ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite repeat_cons_app. reflexivity.
Qed.

(** [B> 1^n  ->  1^n B>] and [B> 2^n  ->  2^n B>] *)
Lemma chain_B1 : forall n l r,
  csteps bigfoot n (cfgR StB l (repeat S1 n ++ r)) = Some (cfgR StB (repeat S1 n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S1 :: l) (repeat S1 n ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite repeat_cons_app. reflexivity.
Qed.

Lemma chain_B2 : forall n l r,
  csteps bigfoot n (cfgR StB l (repeat S2 n ++ r)) = Some (cfgR StB (repeat S2 n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S2 :: l) (repeat S2 n ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite repeat_cons_app. reflexivity.
Qed.

Lemma rep2_cons2 : forall (x y : Sym) n l, rep [x; y] n ++ x :: y :: l = x :: y :: rep [x; y] n ++ l.
Proof.
  induction n; intros; simpl; [reflexivity|]. rewrite IHn. reflexivity.
Qed.

(** [B> (21)^n  ->  (12)^n B>]: the right block [2 1 2 1 ...] is
    [rep [2;1] n]; what is deposited, nearest-first, is [rep [1;2] n]. *)
Lemma chain_B21 : forall n l r,
  csteps bigfoot (2 * n) (cfgR StB l (rep [S2; S1] n ++ r)) = Some (cfgR StB (rep [S1; S2] n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgR StB (S2 :: l) (S1 :: rep [S2; S1] n ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S1 :: S2 :: l) (rep [S2; S1] n ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite rep2_cons2. reflexivity.
Qed.

(** [(12)^n <A  ->  <A (21)^n]: nearest-first the left block [... 1 2]
    is [rep [2;1] n], and the right block [2 1 2 1 ...] is also [rep [2;1] n]. *)
Lemma chain_A12 : forall n l r,
  csteps bigfoot (2 * n) (cfgL StA (rep [S2; S1] n ++ l) r) = Some (cfgL StA l (rep [S2; S1] n ++ r)).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgL StC (S1 :: rep [S2; S1] n ++ l) (S1 :: r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StA (rep [S2; S1] n ++ l) (S2 :: S1 :: r)); [reflexivity|].
  rewrite IHn. unfold cfgL. rewrite rep2_cons2. reflexivity.
Qed.

(** [2^(2k) <C  ->  <C 1^(2k)] and the three siblings. *)
Lemma chain_C2_even : forall k l r,
  csteps bigfoot (2 * k) (cfgL StC (repeat S2 (2 * k) ++ l) r) = Some (cfgL StC l (repeat S1 (2 * k) ++ r)).
Proof.
  induction k; intros l r; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  eapply csteps_S_intro with (c' := cfgL StA (S2 :: repeat S2 (2 * k) ++ l) (S1 :: r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StC (repeat S2 (2 * k) ++ l) (S1 :: S1 :: r)); [reflexivity|].
  rewrite IHk. unfold cfgL. rewrite !repeat_cons_app. reflexivity.
Qed.

Lemma chain_A2_even : forall k l r,
  csteps bigfoot (2 * k) (cfgL StA (repeat S2 (2 * k) ++ l) r) = Some (cfgL StA l (repeat S1 (2 * k) ++ r)).
Proof.
  induction k; intros l r; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  eapply csteps_S_intro with (c' := cfgL StC (S2 :: repeat S2 (2 * k) ++ l) (S1 :: r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StA (repeat S2 (2 * k) ++ l) (S1 :: S1 :: r)); [reflexivity|].
  rewrite IHk. unfold cfgL. rewrite !repeat_cons_app. reflexivity.
Qed.

Lemma chain_C2_odd : forall k l r,
  csteps bigfoot (S (2 * k)) (cfgL StC (repeat S2 (S (2 * k)) ++ l) r)
  = Some (cfgL StA l (repeat S1 (S (2 * k)) ++ r)).
Proof.
  intros k l r.
  eapply csteps_S_intro with (c' := cfgL StA (repeat S2 (2 * k) ++ l) (S1 :: r)); [reflexivity|].
  rewrite chain_A2_even. unfold cfgL. rewrite repeat_cons_app. reflexivity.
Qed.

Lemma chain_A2_odd : forall k l r,
  csteps bigfoot (S (2 * k)) (cfgL StA (repeat S2 (S (2 * k)) ++ l) r)
  = Some (cfgL StC l (repeat S1 (S (2 * k)) ++ r)).
Proof.
  intros k l r.
  eapply csteps_S_intro with (c' := cfgL StC (repeat S2 (2 * k) ++ l) (S1 :: r)); [reflexivity|].
  rewrite chain_C2_even. unfold cfgL. rewrite repeat_cons_app. reflexivity.
Qed.

(** Chain lemmas at the end of the right half-tape. *)
Lemma chain_A1N : forall n l,
  csteps bigfoot n (cfgR StA l (repeat S1 n)) = Some (cfgR StA (repeat S2 n ++ l) []).
Proof.
  intros. eapply csteps_conf_eq; [apply chain_A1 with (r := []) | rewrite app_nil_r | ]; reflexivity.
Qed.
Lemma chain_B1N : forall n l,
  csteps bigfoot n (cfgR StB l (repeat S1 n)) = Some (cfgR StB (repeat S1 n ++ l) []).
Proof.
  intros. eapply csteps_conf_eq; [apply chain_B1 with (r := []) | rewrite app_nil_r | ]; reflexivity.
Qed.
Lemma chain_B21N : forall n l,
  csteps bigfoot (2 * n) (cfgR StB l (rep [S2; S1] n)) = Some (cfgR StB (rep [S1; S2] n ++ l) []).
Proof.
  intros. eapply csteps_conf_eq; [apply chain_B21 with (r := []) | rewrite app_nil_r | ]; reflexivity.
Qed.

(** ** Tactics *)

Lemma fold_repeat1 : forall (x : Sym) n l, x :: repeat x n ++ l = repeat x (S n) ++ l.
Proof. reflexivity. Qed.
Lemma fold_repeat1' : forall (x : Sym) n, x :: repeat x n = repeat x (S n).
Proof. reflexivity. Qed.

(** [hop L]: run the hop lemma [L] from the current configuration and
    continue; the count equation is left for [lia] at the end. *)
Ltac hop L := eapply csteps_trans_eq; [eapply L | | ].
Ltac hop2 L1 L2 := eapply csteps_trans_eq; [first [eapply L1 | eapply L2] | | ].
Ltac stA0 := hop2 sA0N sA0NL.
Ltac stA1 := hop2 sA1L sA1R.
Ltac stA2 := hop2 sA2L sA2R.
Ltac stB0 := hop sB0N.
Ltac stB1 := hop sB1R.
Ltac stB2 := hop sB2R.
Ltac stC1 := hop2 sC1L sC1R.
Ltac stC2 := hop2 sC2L sC2R.
(** Expose the first cells of concrete prefixes. *)
Ltac expose := cbn [Nat.add repeat rep app].
(** Close the run: the current configuration is the target up to list algebra. *)
Ltac fin := eapply csteps_conf_eq; [apply csteps_0 | reflexivity | ].

(** Refold leading copies into a block with a chosen count. *)
Lemma fold_to1 : forall (x : Sym) n n' l, 1 + n = n' -> x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma fold_to2 : forall (x : Sym) n n' l, 2 + n = n' -> x :: x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma fold_to3 : forall (x : Sym) n n' l,
  3 + n = n' -> x :: x :: x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma repeat_count : forall (x : Sym) n n' l, n = n' -> repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.

Lemma split_last : forall (x : Sym) n n' l, n = S n' -> repeat x n ++ l = repeat x n' ++ x :: l.
Proof. intros; subst; rewrite repeat_cons_app; reflexivity. Qed.

Lemma cfgL_eq : forall q l l' r r', l = l' -> r = r' -> cfgL q l r = cfgL q l' r'.
Proof. intros; subst; reflexivity. Qed.
Lemma rep_block_eq : forall (x : Sym) n n' l l', n = n' -> l = l' -> repeat x n ++ l = repeat x n' ++ l'.
Proof. intros; subst; reflexivity. Qed.
Lemma repeat_eq : forall (x : Sym) n n', n = n' -> repeat x n = repeat x n'.
Proof. intros; subst; reflexivity. Qed.

Ltac side_eq :=
  first [ reflexivity
        | (apply rep_block_eq; [lia | reflexivity])
        | (apply repeat_eq; lia) ].
Ltac conf_eq :=
  rewrite ?repeat_cons_app, ?app_nil_r, ?fold_repeat1, ?fold_repeat1';
  first [reflexivity | (apply cfgL_eq; side_eq)].
(** After the hops: the deferred count equations, innermost first. *)
Ltac counts := try reflexivity; lia.

(** ** The partial configuration P(m, n) = 1^m <A 1^n 0^inf *)

Definition P (L : list Sym) (m n : nat) : cconf :=
  cfgL StA (repeat S1 m ++ L) (repeat S1 n).

Lemma P_eq : forall L m m' n n', m = m' -> n = n' -> P L m n = P L m' n'.
Proof. intros; subst; reflexivity. Qed.

(** The wiki's even case: P(m+9, 2k) -> P(m, 2k+11) in 6(2k)+43 steps. *)
Lemma P_even : forall k m L,
  csteps bigfoot (6 * (2 * k) + 43) (P L (9 + m) (2 * k)) = Some (P L m (2 * k + 11)).
Proof.
  intros k m L. unfold P. expose.
  stA1. hop chain_A1N.
  stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2. hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * k) (3 + 2 * k)) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (3 + 2 * k) (2 * (k + 2))) by lia.
  hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (k + 2)) (7 + 2 * k)) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (7 + 2 * k) (2 * (k + 4))) by lia.
  hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  fin. conf_eq.
  all: counts.
Qed.

(** The wiki's odd case: P(m+3, 2k+1) -> P(m, 2k+6) in 6(2k+1)+19 steps. *)
Lemma P_odd : forall k m L,
  csteps bigfoot (6 * S (2 * k) + 19) (P L (3 + m) (S (2 * k))) = Some (P L m (2 * k + 6)).
Proof.
  intros k m L. unfold P. expose.
  rewrite (fold_repeat1' S1 (2 * k)).
  stA1. hop chain_A1N.
  stA0. stB0. stC1.
  expose.
  stA2. hop chain_C2_even.
  stC2. stA1.
  rewrite repeat_cons_app, (fold_to2 S1 (2 * k) (2 + 2 * k)) by lia.
  hop chain_A1.
  stA2.
  rewrite (repeat_count S2 (2 + 2 * k) (2 * (k + 1))) by lia.
  hop chain_C2_even.
  stC2. stA1.
  rewrite repeat_cons_app, (fold_to2 S1 (2 * (k + 1)) (4 + 2 * k)) by lia.
  hop chain_A1.
  stA2.
  rewrite (repeat_count S2 (4 + 2 * k) (2 * (k + 2))) by lia.
  hop chain_C2_even.
  stC2.
  fin. conf_eq.
  all: counts.
Qed.

(** ** The loop: P(12i + r, 2c) -> P(r, 2c + 16i)

    Each round is one even case followed by one odd case, consuming
    twelve 1s on the left for sixteen on the right. *)
Lemma P_loop : forall i r c L,
  csteps bigfoot (24 * c * i + 96 * i * i + 32 * i) (P L (12 * i + r) (2 * c))
  = Some (P L r (2 * c + 16 * i)).
Proof.
  induction i; intros r c L.
  - replace (24 * c * 0 + 96 * 0 * 0 + 32 * 0) with 0 by lia.
    fin. apply P_eq; lia.
  - eapply csteps_trans_eq.
    { eapply csteps_conf_eq; [apply (P_even c (12 * i + r + 3) L) | | reflexivity].
      apply P_eq; lia. }
    eapply csteps_trans_eq.
    { eapply csteps_conf_eq; [apply (P_odd (c + 5) (12 * i + r) L) | | reflexivity].
      apply P_eq; lia. }
    eapply csteps_conf_eq; [apply (IHi r (c + 8) L) | | ]; apply P_eq; lia.
    all: try reflexivity. first [ring | nia].
Qed.

(** ** Concrete tails at the right end of the tape *)

(** [1^3 B> 0^inf  ->  <A 1^4] *)
Lemma tail12 : forall l,
  csteps bigfoot 12 (cfgR StB (S1 :: S1 :: S1 :: l) []) = Some (cfgL StA l (repeat S1 4)).
Proof. reflexivity. Qed.

(** [1^3 2 2 B> 0^inf  ->  <A 1^6] *)
Lemma tail18 : forall l,
  csteps bigfoot 18 (cfgR StB (S2 :: S2 :: S1 :: S1 :: S1 :: l) []) = Some (cfgL StA l (repeat S1 6)).
Proof. reflexivity. Qed.

(** [1^6 2 B> 0^inf  ->  <A 1^10] *)
Lemma tail60 : forall l,
  csteps bigfoot 60 (cfgR StB (S2 :: S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: l) [])
  = Some (cfgL StA l (repeat S1 10)).
Proof. reflexivity. Qed.

Lemma chain_A12N : forall n r,
  csteps bigfoot (2 * n) (cfgL StA (rep [S2; S1] n) r) = Some (cfgL StA [] (rep [S2; S1] n ++ r)).
Proof.
  intros. eapply csteps_conf_eq; [apply chain_A12 with (l := []) | rewrite app_nil_r | ]; reflexivity.
Qed.

(** ** The configurations A'(a, b, c) = 0^inf (12)^a 1^b <A 1^c 0^inf *)

Definition Ap (a b c : nat) : cconf :=
  cfgL StA (repeat S1 b ++ rep [S2; S1] a) (repeat S1 c).

Lemma Ap_P : forall a b c, Ap a b c = P (rep [S2; S1] a) b c.
Proof. reflexivity. Qed.

(** Start a case: run the loop down to P(r, 2(c + 8i)). *)
Ltac start_case i r c a :=
  rewrite Ap_P;
  eapply csteps_trans_eq;
  [ eapply csteps_conf_eq; [apply (P_loop i r c (rep [S2; S1] a)) | apply P_eq; lia | reflexivity] | | ];
  unfold P; expose.

(** b = 12i: A'(a, 12i, 2c) -> A'(a, 16i + 2c - 2, 4). *)
Lemma case0 : forall i c d a, 8 * i + c = S d ->
  csteps bigfoot (4 * a + 96 * i * i + 48 * i + 24 * i * c + 2 * c + 13)
    (Ap a (12 * i) (2 * c)) = Some (Ap a (2 * d) 4).
Proof.
  intros i c d a Hd. start_case i 0 c a.
  hop chain_A12N. stA0. hop chain_B21. hop chain_B1N.
  rewrite rep2_rot, repeat_cons_app, (repeat_count S1 (2 * c + 16 * i) (2 + 2 * d)) by lia.
  expose.
  hop tail12.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** b = 12i + 2: A'(a, 12i+2, 2c) -> A'(a+1, 16i + 2c - 2, 6). *)
Lemma case2 : forall i c d a, 8 * i + c = S d ->
  csteps bigfoot (4 * a + 96 * i * i + 80 * i + 24 * i * c + 6 * c + 29)
    (Ap a (12 * i + 2) (2 * c)) = Some (Ap (S a) (2 * d) 6).
Proof.
  intros i c d a Hd. start_case i 2 c a.
  replace (2 * c + 16 * i) with (2 * (c + 8 * i)) by lia.
  stA1. hop chain_A1N. stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2. hop chain_C2_even.
  stC1. hop chain_A12N. stA0. hop chain_B21. stB2. hop chain_B1.
  stB1. stB2. stB2.
  rewrite rep2_rot.
  change (S2 :: S1 :: rep [S2; S1] a) with (rep [S2; S1] (S a)).
  rewrite (repeat_count S1 (2 * (c + 8 * i)) (2 + 2 * d)) by lia.
  expose.
  hop tail18.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** b = 12i + 4, a >= 1: A'(a+1, 12i+4, 2c) -> A'(a, 16i + 2c + 6, 4). *)
Lemma case4 : forall i c a,
  csteps bigfoot (4 * S a + 96 * i * i + 144 * i + 24 * i * c + 14 * c + 51)
    (Ap (S a) (12 * i + 4) (2 * c)) = Some (Ap a (16 * i + 2 * c + 6) 4).
Proof.
  intros i c a. start_case i 4 c (S a).
  replace (2 * c + 16 * i) with (2 * (c + 8 * i)) by lia.
  stA1. hop chain_A1N. stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2. hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (c + 8 * i)) (3 + 2 * (c + 8 * i))) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (3 + 2 * (c + 8 * i)) (2 * (c + 8 * i + 2))) by lia.
  hop chain_C2_even.
  expose.
  stC2. stA1.
  rewrite repeat_cons_app, (fold_to2 S1 (2 * (c + 8 * i + 2)) (6 + 2 * (c + 8 * i))) by lia.
  hop chain_A1.
  stA2.
  rewrite (repeat_count S2 (6 + 2 * (c + 8 * i)) (2 * (c + 8 * i + 3))) by lia.
  hop chain_C2_even.
  stC2. hop chain_A12N. stA0. hop chain_B21.
  rewrite repeat_cons_app, (fold_to2 S1 (2 * (c + 8 * i + 3)) (8 + 2 * (c + 8 * i))) by lia.
  hop chain_B1.
  rewrite rep2_rot, repeat_cons_app.
  expose.
  hop tail12.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** b = 12i + 6: A'(a, 12i+6, 2c) -> A'(a, 16i + 2c + 2, 10). *)
Lemma case6 : forall i c a,
  csteps bigfoot (4 * a + 96 * i * i + 112 * i + 24 * i * c + 10 * c + 91)
    (Ap a (12 * i + 6) (2 * c)) = Some (Ap a (16 * i + 2 * c + 2) 10).
Proof.
  intros i c a. start_case i 6 c a.
  replace (2 * c + 16 * i) with (2 * (c + 8 * i)) by lia.
  stA1. hop chain_A1N. stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2. hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (c + 8 * i)) (3 + 2 * (c + 8 * i))) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (3 + 2 * (c + 8 * i)) (2 * (c + 8 * i + 2))) by lia.
  hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  hop chain_A12N. stA0. hop chain_B21.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (c + 8 * i + 2)) (7 + 2 * (c + 8 * i))) by lia.
  hop chain_B1. stB2.
  rewrite rep2_rot, repeat_cons_app.
  expose.
  hop tail60.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** b = 12i + 8: A'(a, 12i+8, 2c) -> A'(a+1, 16i + 2c + 6, 4). *)
Lemma case8 : forall i c a,
  csteps bigfoot (4 * a + 96 * i * i + 144 * i + 24 * i * c + 14 * c + 63)
    (Ap a (12 * i + 8) (2 * c)) = Some (Ap (S a) (16 * i + 2 * c + 6) 4).
Proof.
  intros i c a. start_case i 8 c a.
  replace (2 * c + 16 * i) with (2 * (c + 8 * i)) by lia.
  stA1. hop chain_A1N. stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2. hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (c + 8 * i)) (3 + 2 * (c + 8 * i))) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (3 + 2 * (c + 8 * i)) (2 * (c + 8 * i + 2))) by lia.
  hop chain_C2_even.
  stC1. stA1. stA2. stC2.
  stA1.
  rewrite repeat_cons_app, (fold_to3 S1 (2 * (c + 8 * i + 2)) (7 + 2 * (c + 8 * i))) by lia.
  hop chain_A1.
  stA2.
  rewrite repeat_cons_app, (fold_to1 S2 (7 + 2 * (c + 8 * i)) (2 * (c + 8 * i + 4))) by lia.
  hop chain_C2_even.
  stC1. hop chain_A12N. stA0. hop chain_B21. stB2.
  rewrite repeat_cons_app, (fold_to1 S1 (2 * (c + 8 * i + 4)) (9 + 2 * (c + 8 * i))) by lia.
  hop chain_B1.
  rewrite rep2_rot.
  change (S2 :: S1 :: rep [S2; S1] a) with (rep [S2; S1] (S a)).
  expose.
  hop tail12.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** b = 12i + 10: A'(a, 12i+10, 2c) -> A'(a, 16i + 2c + 10, 6). *)
Lemma case10 : forall i c a,
  csteps bigfoot (4 * a + 96 * i * i + 176 * i + 24 * i * c + 18 * c + 103)
    (Ap a (12 * i + 10) (2 * c)) = Some (Ap a (16 * i + 2 * c + 10) 6).
Proof.
  intros i c a. rewrite Ap_P.
  eapply csteps_trans_eq.
  { eapply csteps_conf_eq; [apply (P_loop i 10 c (rep [S2; S1] a)) | apply P_eq; lia | reflexivity]. }
  eapply csteps_trans_eq.
  { eapply csteps_conf_eq; [apply (P_even (c + 8 * i) 1 (rep [S2; S1] a)) | apply P_eq; lia | reflexivity]. }
  unfold P. expose.
  stA1. hop chain_A1N. stA0. stB0. stC1.
  rewrite repeat_cons_app.
  stA2.
  rewrite (split_last S2 (2 * (c + 8 * i) + 11) (2 * (c + 8 * i + 5))) by lia.
  hop chain_C2_even.
  stC2. hop chain_A12N. stA0. hop chain_B21.
  rewrite repeat_cons_app, (fold_to2 S1 (2 * (c + 8 * i + 5)) (12 + 2 * (c + 8 * i))) by lia.
  hop chain_B1. stB2. stB2.
  rewrite rep2_rot, repeat_cons_app.
  expose.
  hop tail18.
  fin. conf_eq.
  all: try reflexivity. nia.
Qed.

(** ** The rules for A(a, b, c) = A'(a, 2b, 2c) = 0^inf (12)^a (11)^b <A (11)^c 0^inf *)

Definition A (a b c : nat) : cconf := Ap a (2 * b) (2 * c).

Lemma Ap_eq : forall a a' b b' c c', a = a' -> b = b' -> c = c' -> Ap a b c = Ap a' b' c'.
Proof. intros; subst; reflexivity. Qed.

Ltac a_rule L := unfold A; eapply csteps_conf_eq; [apply L | apply Ap_eq; lia | apply Ap_eq; lia].

(** A(a, 6k, c) -> A(a, 8k+c-1, 2) when 8k+c >= 1. *)
Lemma rule0 : forall k c d a, 8 * k + c = S d ->
  csteps bigfoot (4 * a + 96 * k * k + 48 * k + 24 * k * c + 2 * c + 13) (A a (6 * k) c)
  = Some (A a d 2).
Proof. intros k c d a H. a_rule (case0 k c d a H). Qed.

(** A(a, 6k+1, c) -> A(a+1, 8k+c-1, 3) when 8k+c >= 1. *)
Lemma rule1 : forall k c d a, 8 * k + c = S d ->
  csteps bigfoot (4 * a + 96 * k * k + 80 * k + 24 * k * c + 6 * c + 29) (A a (6 * k + 1) c)
  = Some (A (S a) d 3).
Proof. intros k c d a H. a_rule (case2 k c d a H). Qed.

(** A(a+1, 6k+2, c) -> A(a, 8k+c+3, 2). *)
Lemma rule2 : forall k c a,
  csteps bigfoot (4 * S a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 51) (A (S a) (6 * k + 2) c)
  = Some (A a (8 * k + c + 3) 2).
Proof. intros k c a. a_rule (case4 k c a). Qed.

(** A(a, 6k+3, c) -> A(a, 8k+c+1, 5). *)
Lemma rule3 : forall k c a,
  csteps bigfoot (4 * a + 96 * k * k + 112 * k + 24 * k * c + 10 * c + 91) (A a (6 * k + 3) c)
  = Some (A a (8 * k + c + 1) 5).
Proof. intros k c a. a_rule (case6 k c a). Qed.

(** A(a, 6k+4, c) -> A(a+1, 8k+c+3, 2). *)
Lemma rule4 : forall k c a,
  csteps bigfoot (4 * a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 63) (A a (6 * k + 4) c)
  = Some (A (S a) (8 * k + c + 3) 2).
Proof. intros k c a. a_rule (case8 k c a). Qed.

(** A(a, 6k+5, c) -> A(a, 8k+c+5, 3). *)
Lemma rule5 : forall k c a,
  csteps bigfoot (4 * a + 96 * k * k + 176 * k + 24 * k * c + 18 * c + 103) (A a (6 * k + 5) c)
  = Some (A a (8 * k + c + 5) 3).
Proof. intros k c a. a_rule (case10 k c a). Qed.

(** ** One rule step as a function on nat *)

Definition rule_nat (a b c : nat) : option (nat * nat * nat * nat) :=
  let k := b / 6 in
  match b mod 6 with
  | 0 => match 8 * k + c with
         | 0 => None
         | S d => Some (a, d, 2, 4 * a + 96 * k * k + 48 * k + 24 * k * c + 2 * c + 13)
         end
  | 1 => match 8 * k + c with
         | 0 => None
         | S d => Some (S a, d, 3, 4 * a + 96 * k * k + 80 * k + 24 * k * c + 6 * c + 29)
         end
  | 2 => match a with
         | 0 => None
         | S a' => Some (a', 8 * k + c + 3, 2, 4 * a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 51)
         end
  | 3 => Some (a, 8 * k + c + 1, 5, 4 * a + 96 * k * k + 112 * k + 24 * k * c + 10 * c + 91)
  | 4 => Some (S a, 8 * k + c + 3, 2, 4 * a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 63)
  | _ => Some (a, 8 * k + c + 5, 3, 4 * a + 96 * k * k + 176 * k + 24 * k * c + 18 * c + 103)
  end.

Lemma A_eq : forall a a' b b' c c', a = a' -> b = b' -> c = c' -> A a b c = A a' b' c'.
Proof. intros; subst; reflexivity. Qed.

Lemma rule_nat_sound : forall a b c a' b' c' s,
  rule_nat a b c = Some (a', b', c', s) ->
  csteps bigfoot s (A a b c) = Some (A a' b' c').
Proof.
  intros a b c a' b' c' s H. unfold rule_nat in H.
  pose proof (Nat.div_mod b 6 ltac:(lia)) as Hb.
  pose proof (Nat.mod_upper_bound b 6 ltac:(lia)) as Hr.
  set (k := b / 6) in *. set (r := b mod 6) in *.
  assert (Hb' : b = 6 * k + r) by lia. clear Hb.
  destruct r as [|[|[|[|[|[|r]]]]]]; try lia.
  - destruct (8 * k + c) as [|d] eqn:Hd; [discriminate|].
    injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule0 k c d a Hd) | apply A_eq; lia | reflexivity].
  - destruct (8 * k + c) as [|d] eqn:Hd; [discriminate|].
    injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule1 k c d a Hd) | apply A_eq; lia | reflexivity].
  - destruct a as [|a0]; [discriminate|].
    injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule2 k c a0) | apply A_eq; lia | reflexivity].
  - injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule3 k c a) | apply A_eq; lia | reflexivity].
  - injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule4 k c a) | apply A_eq; lia | reflexivity].
  - injection H as <- <- <- <-.
    eapply csteps_conf_eq; [apply (rule5 k c a) | apply A_eq; lia | reflexivity].
Qed.

(** From the blank tape: A(2, 1, 2) after 69 steps. *)
Lemma bigfoot_69 : csteps bigfoot 69 c0 = Some (A 2 1 2).
Proof. vm_compute. reflexivity. Qed.
