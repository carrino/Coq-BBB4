(** * Champion: the probable BB(3,3) champion 1RB2LC1RC_2LC---2RB_2LA0LB0RA.

    Following dyuan01's configuration families on the BusyBeaverWiki
    page for this machine,

      A1(m, b, n) = 0^inf 1 2^m <C (22)^b (20)^n 0^inf
      A2(m, b, n) = 0^inf 1 2^m <A 2 (22)^b (20)^n 0^inf
      B (m, b)    = 0^inf 1 2^m <B 0 (20)^b 0^inf

    we prove a complete set of fine-grained rules between these
    families with exact step counts, plus the accelerated loop
    A1(m+2d, b, n+2d) -> A1(m, b+3d, n).  Rules whose result differs
    from the canonical list form only by trailing blanks are stated
    on the lifted configurations ([RL]).  The trajectory from the
    blank tape is run in [ChampionRun]. *)

From Coq Require Import Arith Lia List FunctionalExtensionality.
From SmallBB Require Import Statement CTape.
From BB33 Require Import Lib.
Import ListNotations.

(** ** The machine: 1RB2LC1RC_2LC---2RB_2LA0LB0RA *)

Definition champ : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S2 DL StC)
  | StA, S2 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S2 DL StC)
  | StB, S1 => None
  | StB, S2 => Some (mkTrans S2 DR StB)
  | StC, S0 => Some (mkTrans S2 DL StA)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StC, S2 => Some (mkTrans S0 DR StA)
  end.

(** ** Single steps *)

Lemma cA0N : forall l, csteps champ 1 (cfgR StA l []) = Some (cfgR StB (S1 :: l) []).
Proof. reflexivity. Qed.
Lemma cA0R : forall l r, csteps champ 1 (cfgR StA l (S0 :: r)) = Some (cfgR StB (S1 :: l) r).
Proof. reflexivity. Qed.
Lemma cA0NL : forall r, csteps champ 1 (cfgL StA [] r) = Some (cfgR StB [S1] r).
Proof. reflexivity. Qed.
Lemma cA1L : forall l r, csteps champ 1 (cfgL StA (S1 :: l) r) = Some (cfgL StC l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cA1R : forall l r, csteps champ 1 (cfgR StA l (S1 :: r)) = Some (cfgL StC l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cA2L : forall l r, csteps champ 1 (cfgL StA (S2 :: l) r) = Some (cfgR StC (S1 :: l) r).
Proof. reflexivity. Qed.
Lemma cA2R : forall l r, csteps champ 1 (cfgR StA l (S2 :: r)) = Some (cfgR StC (S1 :: l) r).
Proof. reflexivity. Qed.
Lemma cB0N : forall l, csteps champ 1 (cfgR StB l []) = Some (cfgL StC l [S2]).
Proof. reflexivity. Qed.
Lemma cB0R : forall l r, csteps champ 1 (cfgR StB l (S0 :: r)) = Some (cfgL StC l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cB0NL : forall r, csteps champ 1 (cfgL StB [] r) = Some (cfgL StC [] (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cB0L : forall l r, csteps champ 1 (cfgL StB (S0 :: l) r) = Some (cfgL StC l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cB2R : forall l r, csteps champ 1 (cfgR StB l (S2 :: r)) = Some (cfgR StB (S2 :: l) r).
Proof. reflexivity. Qed.
Lemma cB2L : forall l r, csteps champ 1 (cfgL StB (S2 :: l) r) = Some (cfgR StB (S2 :: l) r).
Proof. reflexivity. Qed.
Lemma cC0N : forall l, csteps champ 1 (cfgR StC l []) = Some (cfgL StA l [S2]).
Proof. reflexivity. Qed.
Lemma cC0R : forall l r, csteps champ 1 (cfgR StC l (S0 :: r)) = Some (cfgL StA l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cC0NL : forall r, csteps champ 1 (cfgL StC [] r) = Some (cfgL StA [] (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cC0L : forall l r, csteps champ 1 (cfgL StC (S0 :: l) r) = Some (cfgL StA l (S2 :: r)).
Proof. reflexivity. Qed.
Lemma cC1L : forall l r, csteps champ 1 (cfgL StC (S1 :: l) r) = Some (cfgL StB l (S0 :: r)).
Proof. reflexivity. Qed.
Lemma cC1R : forall l r, csteps champ 1 (cfgR StC l (S1 :: r)) = Some (cfgL StB l (S0 :: r)).
Proof. reflexivity. Qed.
Lemma cC2L : forall l r, csteps champ 1 (cfgL StC (S2 :: l) r) = Some (cfgR StA (S0 :: l) r).
Proof. reflexivity. Qed.
Lemma cC2R : forall l r, csteps champ 1 (cfgR StC l (S2 :: r)) = Some (cfgR StA (S0 :: l) r).
Proof. reflexivity. Qed.

(** After a hop, unification may leave [ctl]/[chd] residues on constructor
    lists; normalise them away so later syntactic rewrites see plain lists. *)
Ltac tidy := cbn [ctl chd].
Ltac hop L := eapply csteps_trans_eq; [eapply L | tidy | ].
Ltac hop2 L1 L2 := eapply csteps_trans_eq; [first [eapply L1 | eapply L2] | tidy | ].
Ltac hop3 L1 L2 L3 := eapply csteps_trans_eq; [first [eapply L1 | eapply L2 | eapply L3] | tidy | ].
Ltac stA0 := hop3 cA0R cA0N cA0NL.
Ltac stA1 := hop2 cA1L cA1R.
Ltac stA2 := hop2 cA2L cA2R.
Ltac stB0 := eapply csteps_trans_eq; [first [eapply cB0R | eapply cB0N | eapply cB0L | eapply cB0NL] | tidy | ].
Ltac stB2 := hop2 cB2R cB2L.
Ltac stC0 := eapply csteps_trans_eq; [first [eapply cC0R | eapply cC0N | eapply cC0L | eapply cC0NL] | tidy | ].
Ltac stC1 := hop2 cC1L cC1R.
Ltac stC2 := hop2 cC2L cC2R.
Ltac expose := cbn [Nat.add repeat rep app ctl chd].
Ltac fin := eapply csteps_conf_eq; [apply csteps_0 | reflexivity | ].
Ltac counts := try reflexivity; lia.

(** ** Block algebra *)

Lemma rep2_cons2 : forall (x y : Sym) n l, rep [x; y] n ++ x :: y :: l = x :: y :: rep [x; y] n ++ l.
Proof. induction n; intros; simpl; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma rep_app_w : forall w n l, rep w n ++ w ++ l = rep w (S n) ++ l.
Proof.
  induction n; intros; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite <- app_assoc, IHn. simpl. rewrite <- !app_assoc. reflexivity.
Qed.

(** [(20)^(2k) = (2020)^k] and the like. *)
Lemma rep_dbl : forall w k, rep w (2 * k) = rep (w ++ w) k.
Proof.
  induction k; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [rep]. rewrite IHk, app_assoc. reflexivity.
Qed.

Lemma fold_repeat1 : forall (x : Sym) n l, x :: repeat x n ++ l = repeat x (S n) ++ l.
Proof. reflexivity. Qed.
Lemma fold_repeat1' : forall (x : Sym) n, x :: repeat x n = repeat x (S n).
Proof. reflexivity. Qed.
Lemma fold_to1 : forall (x : Sym) n n' l, 1 + n = n' -> x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma fold_to2 : forall (x : Sym) n n' l, 2 + n = n' -> x :: x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma fold_to3 : forall (x : Sym) n n' l,
  3 + n = n' -> x :: x :: x :: repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma repeat_count : forall (x : Sym) n n' l, n = n' -> repeat x n ++ l = repeat x n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma rep_count : forall w n n' l, n = n' -> rep w n ++ l = rep w n' ++ l.
Proof. intros; subst; reflexivity. Qed.
Lemma split_last : forall (x : Sym) n n' l, n = S n' -> repeat x n ++ l = repeat x n' ++ x :: l.
Proof. intros; subst; rewrite repeat_cons_app; reflexivity. Qed.

(** ** Shift rules *)

(** [B> 2^n -> 2^n B>] *)
Lemma ch_B2 : forall n l r,
  csteps champ n (cfgR StB l (repeat S2 n ++ r)) = Some (cfgR StB (repeat S2 n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S2 :: l) (repeat S2 n ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite repeat_cons_app. reflexivity.
Qed.

(** [A> (22)^n -> (10)^n A>]: deposits, nearest-first, [rep [0;1] n]. *)
Lemma ch_A22 : forall n l r,
  csteps champ (2 * n) (cfgR StA l (repeat S2 (2 * n) ++ r))
  = Some (cfgR StA (rep [S0; S1] n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgR StC (S1 :: l) (S2 :: repeat S2 (2 * n) ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StA (S0 :: S1 :: l) (repeat S2 (2 * n) ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite rep2_cons2. reflexivity.
Qed.

(** [C> (22)^n -> (01)^n C>]: deposits [rep [1;0] n]. *)
Lemma ch_C22 : forall n l r,
  csteps champ (2 * n) (cfgR StC l (repeat S2 (2 * n) ++ r))
  = Some (cfgR StC (rep [S1; S0] n ++ l) r).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgR StA (S0 :: l) (S2 :: repeat S2 (2 * n) ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StC (S1 :: S0 :: l) (repeat S2 (2 * n) ++ r)); [reflexivity|].
  rewrite IHn. unfold cfgR. rewrite rep2_cons2. reflexivity.
Qed.

(** [(10)^n <C -> <C (22)^n]: the left block is [rep [0;1] n] nearest-first. *)
Lemma ch_10L : forall n l r,
  csteps champ (2 * n) (cfgL StC (rep [S0; S1] n ++ l) r)
  = Some (cfgL StC l (repeat S2 (2 * n) ++ r)).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgL StA (S1 :: rep [S0; S1] n ++ l) (S2 :: r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StC (rep [S0; S1] n ++ l) (S2 :: S2 :: r)); [reflexivity|].
  rewrite IHn. unfold cfgL. rewrite !repeat_cons_app. reflexivity.
Qed.

(** [(01)^n <C -> <C (20)^n]: the left block is [rep [1;0] n] nearest-first. *)
Lemma ch_01L : forall n l r,
  csteps champ (2 * n) (cfgL StC (rep [S1; S0] n ++ l) r)
  = Some (cfgL StC l (rep [S2; S0] n ++ r)).
Proof.
  induction n; intros l r; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  eapply csteps_S_intro with (c' := cfgL StB (S0 :: rep [S1; S0] n ++ l) (S0 :: r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StC (rep [S1; S0] n ++ l) (S2 :: S0 :: r)); [reflexivity|].
  rewrite IHn. unfold cfgL. rewrite rep2_cons2. reflexivity.
Qed.

(** [C> (2020)^k -> (0101)^k C>] in 6k steps: deposits [rep [1;0;1;0] k]. *)
Lemma ch_C2020 : forall k l r,
  csteps champ (6 * k) (cfgR StC l (rep [S2; S0; S2; S0] k ++ r))
  = Some (cfgR StC (rep [S1; S0; S1; S0] k ++ l) r).
Proof.
  induction k; intros l r; [reflexivity|].
  replace (6 * S k) with (S (S (S (S (S (S (6 * k))))))) by lia.
  cbn [rep app].
  eapply csteps_S_intro with (c' := cfgR StA (S0 :: l) (S0 :: S2 :: S0 :: rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S1 :: S0 :: l) (S2 :: S0 :: rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StB (S2 :: S1 :: S0 :: l) (S0 :: rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgL StC (S2 :: S1 :: S0 :: l) (S2 :: rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StA (S0 :: S1 :: S0 :: l) (S2 :: rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  eapply csteps_S_intro with (c' := cfgR StC (S1 :: S0 :: S1 :: S0 :: l) (rep [S2; S0; S2; S0] k ++ r)); [reflexivity|].
  rewrite IHk. unfold cfgR.
  change (S1 :: S0 :: S1 :: S0 :: l) with ([S1; S0; S1; S0] ++ l).
  rewrite rep_app_w. reflexivity.
Qed.

Lemma ch_A22N : forall n l,
  csteps champ (2 * n) (cfgR StA l (repeat S2 (2 * n))) = Some (cfgR StA (rep [S0; S1] n ++ l) []).
Proof.
  intros. eapply csteps_conf_eq; [apply ch_A22 with (r := []) | rewrite app_nil_r | ]; reflexivity.
Qed.
Lemma ch_C2020N : forall k l,
  csteps champ (6 * k) (cfgR StC l (rep [S2; S0; S2; S0] k)) = Some (cfgR StC (rep [S1; S0; S1; S0] k ++ l) []).
Proof.
  intros. eapply csteps_conf_eq; [apply ch_C2020 with (r := []) | rewrite app_nil_r | ]; reflexivity.
Qed.

(** ** The configuration families *)

Definition LB (m : nat) : list Sym := repeat S2 m ++ [S1].          (* 0^inf 1 2^m, nearest-first *)
Definition A1c (m b n : nat) : cconf := cfgL StC (LB m) (repeat S2 (2 * b) ++ rep [S2; S0] n).
Definition A2c (m b n : nat) : cconf := cfgL StA (LB m) (S2 :: repeat S2 (2 * b) ++ rep [S2; S0] n).
Definition Bc (m b : nat) : cconf := cfgL StB (LB m) (S0 :: rep [S2; S0] b).

(** ** Rules on lifted configurations

    [RL s c c']: [s] steps of the abstract machine take [lift c] to
    [lift c'].  List-level runs give [RL] facts, and trailing blanks
    on a half-tape do not matter. *)

Definition RL (s : nat) (c c' : cconf) : Prop := stepn champ s (lift c) = Some (lift c').

Lemma RL_csteps : forall s c c', csteps champ s c = Some c' -> RL s c c'.
Proof. intros; apply csteps_lift; assumption. Qed.

Lemma RL_trans : forall n m c c' c'', RL n c c' -> RL m c' c'' -> RL (n + m) c c''.
Proof. unfold RL; intros; rewrite stepn_add, H; assumption. Qed.

Lemma RL_trans_eq : forall k n m c c' c'',
  RL n c c' -> RL m c' c'' -> k = n + m -> RL k c c''.
Proof. intros; subst; eapply RL_trans; eauto. Qed.

Lemma RL_eq : forall s c1 c1' c2 c2',
  RL s c1 c1' -> lift c1 = lift c2 -> lift c1' = lift c2' -> RL s c2 c2'.
Proof. unfold RL; intros; rewrite <- H0, <- H1; assumption. Qed.

Lemma lift_side_rpad : forall r, lift_side (r ++ [S0]) = lift_side r.
Proof.
  intros r. apply functional_extensionality; intro n. unfold lift_side, nthb.
  destruct (Nat.lt_ge_cases n (length r)) as [H|H].
  - apply app_nth1; assumption.
  - rewrite app_nth2 by assumption. rewrite (nth_overflow r S0 H).
    destruct (n - length r) as [|k]; [reflexivity | destruct k; reflexivity].
Qed.

(** A trailing blank on the right half-tape is invisible. *)
Lemma lift_rpad : forall q l h r, lift (q, (l, h, r ++ [S0])) = lift (q, (l, h, r)).
Proof. intros. unfold lift, lift_tape. simpl. rewrite lift_side_rpad. reflexivity. Qed.

Lemma lift_rpad_L : forall q l r, lift (cfgL q l (r ++ [S0])) = lift (cfgL q l r).
Proof. intros. unfold cfgL. apply lift_rpad. Qed.

(** Padding on the right. *)
Lemma lift_pad_eq : forall q l r r', r = r' ++ [S0] -> lift (cfgL q l r) = lift (cfgL q l r').
Proof. intros; subst; apply lift_rpad_L. Qed.

Lemma cfgL_eq : forall q l l' r r', l = l' -> r = r' -> cfgL q l r = cfgL q l' r'.
Proof. intros; subst; reflexivity. Qed.
Lemma rep_block_eq : forall (x : Sym) n n' l l', n = n' -> l = l' -> repeat x n ++ l = repeat x n' ++ l'.
Proof. intros; subst; reflexivity. Qed.
Lemma repeat_eq : forall (x : Sym) n n', n = n' -> repeat x n = repeat x n'.
Proof. intros; subst; reflexivity. Qed.
Lemma A1c_eq : forall m m' b b' n n', m = m' -> b = b' -> n = n' -> A1c m b n = A1c m' b' n'.
Proof. intros; subst; reflexivity. Qed.
Lemma A2c_eq : forall m m' b b' n n', m = m' -> b = b' -> n = n' -> A2c m b n = A2c m' b' n'.
Proof. intros; subst; reflexivity. Qed.
Lemma Bc_eq : forall m m' b b', m = m' -> b = b' -> Bc m b = Bc m' b'.
Proof. intros; subst; reflexivity. Qed.

Ltac side_eq :=
  first [ reflexivity
        | (apply rep_block_eq; [lia | reflexivity])
        | (apply repeat_eq; lia)
        | (apply rep_count; lia) ].
Ltac conf_eq :=
  rewrite ?repeat_cons_app, ?app_nil_r, ?fold_repeat1, ?fold_repeat1';
  first [reflexivity | (apply cfgL_eq; side_eq)].
Ltac unf := unfold A1c, A2c, Bc, LB; rewrite ?Nat.mul_0_r, ?app_nil_r.
(** A list-level run, then the padding fix-up. *)
Ltac rl_run c := eapply RL_eq with (c1 := c); [apply RL_csteps; unf; expose | reflexivity | ].
Ltac fin' := eapply csteps_conf_eq; [apply csteps_0 | reflexivity | reflexivity].

(** ** The rules *)

(** R1: A1(m+1, b, n+1) -> A2(m, b+1, n), 5 + 4b steps. *)
Lemma R1 : forall m b n, csteps champ (5 + 4 * b) (A1c (S m) b (S n)) = Some (A2c m (S b) n).
Proof.
  intros; unf; expose.
  stC2. hop ch_A22. stA2. stC0. stA1. hop ch_10L. stC0.
  fin. conf_eq.
  all: counts.
Qed.

(** R3: A2(m+1, b, n+1) -> A1(m, b+2, n), 7 + 4b steps. *)
Lemma R3 : forall m b n, csteps champ (7 + 4 * b) (A2c (S m) b (S n)) = Some (A1c m (b + 2) n).
Proof.
  intros; unf; expose.
  stA2. stC2. hop ch_A22. stA2. stC0. stA1. hop ch_10L. stC0. stA1.
  fin. conf_eq.
  all: counts.
Qed.

(** The accelerated loop: A1(m+2d, b, n+2d) -> A1(m, b+3d, n). *)
Lemma loop_A1 : forall d m b n,
  csteps champ (12 * d * d + 4 * d + 8 * b * d) (A1c (m + 2 * d) b (n + 2 * d))
  = Some (A1c m (b + 3 * d) n).
Proof.
  induction d as [|d IH]; intros m b n.
  - replace (12 * 0 * 0 + 4 * 0 + 8 * b * 0) with 0 by nia.
    fin. apply A1c_eq; lia.
  - eapply csteps_trans_eq.
    { eapply csteps_conf_eq; [apply (R1 (S (m + 2 * d)) b (S (n + 2 * d))) | apply A1c_eq; lia | reflexivity]. }
    eapply csteps_trans_eq.
    { eapply csteps_conf_eq; [apply (R3 (m + 2 * d) (S b) (n + 2 * d)) | apply A2c_eq; lia | reflexivity]. }
    eapply csteps_conf_eq; [apply (IH m (S b + 2) n) | apply A1c_eq; lia | apply A1c_eq; lia].
    all: try reflexivity. first [ring | nia].
Qed.

(** R5: A1(0, 0, n) -> B(2, n), 5 steps. *)
Lemma R5 : forall n, csteps champ 5 (A1c 0 0 n) = Some (Bc 2 n).
Proof.
  intros; unf; expose.
  stC1. stB0. stC0. stA0. stB2.
  fin. conf_eq.
  all: counts.
Qed.

(** R10: A2(0, b, n+1) -> B(2b+4, n), 6 + 2b steps. *)
Lemma R10 : forall b n, csteps champ (6 + 2 * b) (A2c 0 b (S n)) = Some (Bc (2 * b + 4) n).
Proof.
  intros; unf; expose.
  stA1. stC0. stA0.
  rewrite (fold_to3 S2 (2 * b) (2 * b + 3)) by lia.
  hop ch_B2.
  fin.
  rewrite (repeat_count S2 (2 * b + 4) (S (2 * b + 3))) by lia. reflexivity.
  all: counts.
Qed.

(** R14: B(m+1, 2k+2) -> A2(m, 2k+3, 0), 10k + 17 steps. *)
Lemma R14 : forall m k, csteps champ (10 * k + 17) (Bc (S m) (2 * k + 2)) = Some (A2c m (2 * k + 3) 0).
Proof.
  intros; unf.
  replace (2 * k + 2) with (2 * S k) by lia. rewrite (rep_dbl [S2; S0] (S k)). expose.
  stB2. stB0. stC2. stA2.
  change (S2 :: S0 :: S2 :: S0 :: rep [S2; S0; S2; S0] k) with (rep [S2; S0; S2; S0] (S k)).
  hop ch_C2020N. stC0.
  change (rep [S1; S0; S1; S0] (S k)) with (rep ([S1; S0] ++ [S1; S0]) (S k)).
  rewrite <- rep_dbl.
  change (S1 :: S0 :: repeat S2 m ++ [S1]) with ([S1; S0] ++ repeat S2 m ++ [S1]).
  rewrite rep_app_w.
  rewrite (rep_count [S1; S0] (S (2 * S k)) (S (2 * k + 2))) by lia. expose.
  stA1.
  rewrite <- rep2_rot_app.
  hop ch_10L. stC0.
  fin. conf_eq.
  all: counts.
Qed.

Ltac padL := unf; expose; symmetry; apply lift_pad_eq;
             rewrite ?rep_add; expose; rewrite <- ?app_assoc; expose;
             rewrite ?repeat_cons_app; reflexivity.
Ltac padR := unf; expose; apply lift_pad_eq;
             rewrite ?rep_add; expose; rewrite <- ?app_assoc; expose;
             rewrite ?repeat_cons_app; reflexivity.

(** R2: A1(m+1, b, 0) -> A1(m, 0, b+2), 5 + 4b steps. *)
Lemma R2 : forall m b, RL (5 + 4 * b) (A1c (S m) b 0) (A1c m 0 (b + 2)).
Proof.
  intros.
  eapply RL_eq with (c1 := A1c (S m) b 0) (c1' := cfgL StC (LB m) (rep [S2; S0] b ++ [S2; S0; S2])).
  - apply RL_csteps. unf; expose.
    stC2. hop ch_A22N. stA0. stB0. stC1.
    rewrite rep2_rot_app.
    stB0. hop ch_01L.
    fin'.
    all: counts.
  - reflexivity.
  - padL.
Qed.

(** R4: A2(m+1, b, 0) -> B(m, b+2), 7 + 4b steps. *)
Lemma R4 : forall m b, RL (7 + 4 * b) (A2c (S m) b 0) (Bc m (b + 2)).
Proof.
  intros.
  eapply RL_eq with (c1 := A2c (S m) b 0) (c1' := cfgL StB (LB m) (S0 :: rep [S2; S0] b ++ [S2; S0; S2])).
  - apply RL_csteps. unf; expose.
    stA2. stC2. hop ch_A22N. stA0. stB0. stC1.
    rewrite rep2_rot_app.
    stB0. hop ch_01L. stC1.
    fin'.
    all: counts.
  - reflexivity.
  - padL.
Qed.

(** R6: A1(0, b+1, 0) -> A1(2, b+1, 1), 7 steps. *)
Lemma R6 : forall b, RL 7 (A1c 0 (S b) 0) (A1c 2 (S b) 1).
Proof.
  intros.
  eapply RL_eq with (c1 := A1c 0 (S b) 0) (c1' := cfgL StC [S2; S2; S1] (S2 :: S2 :: S2 :: repeat S2 (2 * b))).
  - apply RL_csteps. unf. replace (2 * S b) with (S (S (2 * b))) by lia. expose.
    stC1. stB0. stC0. stA0. stB2. stB2. stB0.
    fin'.
    all: counts.
  - reflexivity.
  - unf. replace (2 * S b) with (S (S (2 * b))) by lia. padL.
Qed.

(** R7: A1(0, b+1, 1) -> A1(2, b+2, 0), 7 steps. *)
Lemma R7 : forall b, RL 7 (A1c 0 (S b) 1) (A1c 2 (b + 2) 0).
Proof.
  intros.
  eapply RL_eq with (c1 := A1c 0 (S b) 1)
                    (c1' := cfgL StC [S2; S2; S1] (S2 :: S2 :: S2 :: repeat S2 (2 * b) ++ [S2; S0])).
  - apply RL_csteps. unf. replace (2 * S b) with (S (S (2 * b))) by lia. expose.
    stC1. stB0. stC0. stA0. stB2. stB2. stB0.
    fin'.
    all: counts.
  - reflexivity.
  - unf. replace (2 * (b + 2)) with (S (S (S (S (2 * b))))) by lia. padR.
Qed.

(** R8: A1(0, b+1, 2k+2) -> A2(1, b+2k+4, 0), 4b + 10k + 26 steps. *)
Lemma R8 : forall b k,
  csteps champ (4 * b + 10 * k + 26) (A1c 0 (S b) (2 * k + 2)) = Some (A2c 1 (b + 2 * k + 4) 0).
Proof.
  intros. unf.
  replace (2 * S b) with (S (S (2 * b))) by lia.
  replace (2 * k + 2) with (2 * S k) by lia. rewrite (rep_dbl [S2; S0] (S k)). expose.
  stC1. stB0. stC0. stA0. stB2. stB2. stB0. stC2.
  rewrite repeat_cons_app, !fold_repeat1.
  rewrite (repeat_count S2 (S (S (S (S (2 * b))))) (2 * (b + 2))) by lia.
  hop ch_A22. stA0. stB2. stB0. stC2. stA2. hop ch_C2020N. stC0.
  change (rep [S1; S0; S1; S0] k) with (rep ([S1; S0] ++ [S1; S0]) k).
  rewrite <- rep_dbl, (rep2_rot_app S0 S1 (b + 2)).
  change (S1 :: S0 :: S1 :: S0 :: rep [S1; S0] (b + 2) ++ [S2; S1])
    with (rep [S1; S0] (S (S (b + 2))) ++ [S2; S1]).
  rewrite app_assoc, <- rep_add.
  rewrite (rep_count [S1; S0] (2 * k + S (S (b + 2))) (S (2 * k + b + 3))) by lia. expose.
  stA1.
  rewrite <- rep2_rot_app.
  hop ch_10L. stC0.
  fin. conf_eq.
  all: counts.
Qed.

(** R9: A1(0, b+1, 2k+3) -> A1(1, 0, b+2k+6), 4b + 10k + 30 steps. *)
Lemma R9 : forall b k,
  RL (4 * b + 10 * k + 30) (A1c 0 (S b) (2 * k + 3)) (A1c 1 0 (b + 2 * k + 6)).
Proof.
  intros.
  eapply RL_eq with (c1 := A1c 0 (S b) (2 * k + 3))
                    (c1' := cfgL StC [S2; S1] (rep [S2; S0] (2 * k + b + 5) ++ [S2])).
  - apply RL_csteps. unf.
    replace (2 * S b) with (S (S (2 * b))) by lia.
    replace (2 * k + 3) with (2 * S k + 1) by lia. rewrite rep_add, (rep_dbl [S2; S0] (S k)). expose.
    stC1. stB0. stC0. stA0. stB2. stB2. stB0. stC2.
    rewrite repeat_cons_app, !fold_repeat1.
    rewrite (repeat_count S2 (S (S (S (S (2 * b))))) (2 * (b + 2))) by lia.
    hop ch_A22. stA0. stB2. stB0. stC2. stA2. hop ch_C2020. stC2. stA0. stB0.
    change (rep [S1; S0; S1; S0] k) with (rep ([S1; S0] ++ [S1; S0]) k).
    rewrite <- rep_dbl, (rep2_rot_app S0 S1 (b + 2)).
    change (S1 :: S0 :: S1 :: S0 :: rep [S1; S0] (b + 2) ++ [S2; S1])
      with (rep [S1; S0] (S (S (b + 2))) ++ [S2; S1]).
    rewrite app_assoc, <- rep_add.
    change (S1 :: S0 :: rep [S1; S0] (2 * k + S (S (b + 2))) ++ [S2; S1])
      with (rep [S1; S0] (S (2 * k + S (S (b + 2)))) ++ [S2; S1]).
    rewrite (rep_count [S1; S0] (S (2 * k + S (S (b + 2)))) (2 * k + b + 5)) by lia.
    hop ch_01L.
    fin'.
    all: counts.
  - reflexivity.
  - replace (b + 2 * k + 6) with (2 * k + b + 5 + 1) by lia. padL.
Qed.

(** R11: A2(0, b, 0) -> B(2b+3, 0), 5 + 2b steps. *)
Lemma R11 : forall b, RL (5 + 2 * b) (A2c 0 b 0) (Bc (2 * b + 3) 0).
Proof.
  intros.
  eapply RL_eq with (c1 := A2c 0 b 0) (c1' := cfgR StB (repeat S2 (2 + 2 * b) ++ [S1]) [S2]).
  - apply RL_csteps. unf; expose.
    stA1. stC0. stA0.
    rewrite ?app_nil_r.
    replace (S2 :: S2 :: S2 :: repeat S2 (2 * b)) with (repeat S2 (2 + 2 * b) ++ [S2])
      by (rewrite repeat_cons_app, app_nil_r; reflexivity).
    hop ch_B2.
    fin'.
    all: counts.
  - reflexivity.
  - unf. rewrite (repeat_count S2 (2 * b + 3) (S (2 + 2 * b))) by lia. expose.
    unfold cfgL, cfgR. cbn [ctl chd].
    change [S0] with ([] ++ [S0]). symmetry. apply lift_rpad.
Qed.

(** R12: B(m+1, 0) -> A1(m+1, 0, 1), 2 steps. *)
Lemma R12 : forall m, RL 2 (Bc (S m) 0) (A1c (S m) 0 1).
Proof.
  intros.
  eapply RL_eq with (c1 := Bc (S m) 0) (c1' := cfgL StC (S2 :: repeat S2 m ++ [S1]) [S2]).
  - apply RL_csteps. unf; expose. stB2. stB0. fin'. all: counts.
  - reflexivity.
  - padL.
Qed.

(** R13: B(m+1, 1) -> A1(m+1, 1, 0), 2 steps. *)
Lemma R13 : forall m, RL 2 (Bc (S m) 1) (A1c (S m) 1 0).
Proof.
  intros.
  eapply RL_eq with (c1 := Bc (S m) 1) (c1' := cfgL StC (S2 :: repeat S2 m ++ [S1]) [S2; S2; S0]).
  - apply RL_csteps. unf; expose. stB2. stB0. fin'. all: counts.
  - reflexivity.
  - padR.
Qed.

(** R15: B(m+1, 2k+3) -> A1(m, 0, 2k+5), 10k + 21 steps. *)
Lemma R15 : forall m k, RL (10 * k + 21) (Bc (S m) (2 * k + 3)) (A1c m 0 (2 * k + 5)).
Proof.
  intros.
  eapply RL_eq with (c1 := Bc (S m) (2 * k + 3)) (c1' := cfgL StC (LB m) (rep [S2; S0] (2 * k + 4) ++ [S2])).
  - apply RL_csteps. unf.
    replace (2 * k + 3) with (2 * S k + 1) by lia. rewrite rep_add, (rep_dbl [S2; S0] (S k)). expose.
    stB2. stB0. stC2. stA2.
    change (S2 :: S0 :: S2 :: S0 :: rep [S2; S0; S2; S0] k ++ [S2; S0])
      with (rep [S2; S0; S2; S0] (S k) ++ [S2; S0]).
    hop ch_C2020. stC2. stA0. stB0.
    change (rep [S1; S0; S1; S0] (S k)) with (rep ([S1; S0] ++ [S1; S0]) (S k)).
    rewrite <- rep_dbl.
    change (S1 :: S0 :: repeat S2 m ++ [S1]) with ([S1; S0] ++ repeat S2 m ++ [S1]).
    rewrite rep_app_w.
    change (S1 :: S0 :: rep [S1; S0] (S (2 * S k)) ++ repeat S2 m ++ [S1])
      with (rep [S1; S0] (S (S (2 * S k))) ++ repeat S2 m ++ [S1]).
    rewrite (rep_count [S1; S0] (S (S (2 * S k))) (2 * k + 4)) by lia.
    hop ch_01L.
    fin'.
    all: counts.
  - reflexivity.
  - replace (2 * k + 5) with (2 * k + 4 + 1) by lia. padL.
Qed.
