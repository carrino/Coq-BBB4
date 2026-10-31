(** * Lib: symbolic-execution toolkit for long-run lower bounds.

    Configurations are [CTape.cconf]: a state and a list tape
    [(left, head, right)] with the half-tapes nearest-first and the
    trailing blanks implicit.  For symbolic proofs it is convenient to
    write a configuration by which side the head sits on:

    - [cfgL q l r] -- head on the first cell of [l] (the wiki's "l <q r");
    - [cfgR q l r] -- head on the first cell of [r] (the wiki's "l q> r").

    Both are the same [cconf] once the list is a cons; an empty side
    is the implicit blank.  [rep w n] is the block [w] repeated [n]
    times, nearest-first on whichever side it is used. *)

From Coq Require Import Arith NArith Lia List.
From SmallBB Require Import Statement CTape.
Import ListNotations.

Definition cfgL (q : St) (l r : list Sym) : cconf := (q, (ctl l, chd l, r)).
Definition cfgR (q : St) (l r : list Sym) : cconf := (q, (l, chd r, ctl r)).

Lemma cfgL_cons : forall q x l r, cfgL q (x :: l) r = (q, (l, x, r)).
Proof. reflexivity. Qed.
Lemma cfgR_cons : forall q x l r, cfgR q l (x :: r) = (q, (l, x, r)).
Proof. reflexivity. Qed.
Lemma cfgL_nil : forall q r, cfgL q [] r = (q, ([], S0, r)).
Proof. reflexivity. Qed.
Lemma cfgR_nil : forall q l, cfgR q l [] = (q, (l, S0, [])).
Proof. reflexivity. Qed.

(** ** Step algebra *)

Lemma csteps_trans : forall tm n m c c' c'',
  csteps tm n c = Some c' -> csteps tm m c' = Some c'' ->
  csteps tm (n + m) c = Some c''.
Proof. intros tm n m c c' c'' H1 H2. rewrite csteps_add, H1. exact H2. Qed.

(** The workhorse: chain two runs and discharge the count equation
    at the end (by [lia]), so hop lemmas can be composed without
    computing step counts up front. *)
Lemma csteps_trans_eq : forall tm k n m c c' c'',
  csteps tm n c = Some c' -> csteps tm m c' = Some c'' -> k = n + m ->
  csteps tm k c = Some c''.
Proof. intros; subst; eapply csteps_trans; eauto. Qed.

Lemma csteps_0 : forall tm c, csteps tm 0 c = Some c.
Proof. reflexivity. Qed.

Lemma csteps_S_intro : forall tm n c c' c'',
  cstep tm c = Some c' -> csteps tm n c' = Some c'' ->
  csteps tm (S n) c = Some c''.
Proof. intros tm n c c' c'' H1 H2. simpl. rewrite H1. exact H2. Qed.

(** Rewriting the start or end configuration. *)
Lemma csteps_conf_eq : forall tm n c1 c2 c1' c2',
  csteps tm n c1 = Some c1' -> c1 = c2 -> c1' = c2' ->
  csteps tm n c2 = Some c2'.
Proof. intros; subst; assumption. Qed.

(** ** Blocks *)

Fixpoint rep (w : list Sym) (n : nat) : list Sym :=
  match n with
  | 0 => []
  | S m => w ++ rep w m
  end.

Lemma rep_S : forall w n, rep w (S n) = w ++ rep w n.
Proof. reflexivity. Qed.

Lemma rep_add : forall w n m, rep w (n + m) = rep w n ++ rep w m.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma repeat_S : forall (x : Sym) n, repeat x (S n) = x :: repeat x n.
Proof. reflexivity. Qed.

Lemma repeat_add : forall (x : Sym) n m,
  repeat x (n + m) = repeat x n ++ repeat x m.
Proof. intros; apply repeat_app. Qed.

Lemma repeat_cons_app : forall (x : Sym) n l,
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma repeat_app_assoc : forall (x : Sym) n m l,
  repeat x n ++ repeat x m ++ l = repeat x (n + m) ++ l.
Proof. intros. rewrite repeat_add, app_assoc. reflexivity. Qed.

(** Rotating a two-symbol comb: [x y x y ... x y x = x y x y ... x y x]. *)
Lemma rep2_rot_app : forall x y n l, rep [x; y] n ++ x :: l = x :: rep [y; x] n ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma rep2_rot : forall x y n, rep [x; y] n ++ [x] = x :: rep [y; x] n.
Proof. intros. rewrite rep2_rot_app, app_nil_r. reflexivity. Qed.

(** ** From the computable configurations to the abstract machine *)

Lemma csteps_lift_stepn : forall tm n c c',
  csteps tm n c = Some c' -> stepn tm n (lift c) = Some (lift c').
Proof. intros; apply csteps_lift; assumption. Qed.

(** A run of [n] steps from the initial configuration shows the
    machine has not halted within the first [n] steps. *)
Lemma csteps_c0_no_halt : forall tm n c,
  csteps tm n c0 = Some c ->
  forall m, m <= n -> stepn tm m InitES <> None.
Proof.
  intros tm n c H m Hm.
  destruct (csteps_prefix tm m n c0 c Hm H) as (cm & Hcm & _).
  rewrite <- lift_c0, (csteps_lift_stepn _ _ _ _ Hcm). discriminate.
Qed.

(** ** The target

    The BB(3,3) champion 0RB2LA1RA_1LA2RB1RC_1RZ1LB1LC halts after
    119,112,334,170,342,541 steps (Terry and Shawn Ligocki, 2007). *)
Definition bb33_champion_steps : N := 119112334170342541.
