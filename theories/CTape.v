(** * CTape: computable configurations.

    The abstract [Tape] of [BBB4_Statement] carries half-tapes as
    functions, which is the right shape for stating theorems but not
    for computing.  Reflective checkers instead run on [cconf]:
    finite-support configurations whose half-tapes are lists (nearest
    cell first, trailing blanks implicit), with

    - [lift]: the denotation into [ExecState];
    - [cstep]/[csteps]: computable stepping, commuting with the
      abstract [step]/[stepn] under [lift] ([cstep_lift],
      [csteps_lift]);
    - [ceqb]: decidable configuration equality up to blank padding,
      sound for the denotation ([ceqb_lift]).

    Equality of denoted tapes is functional, so this file (alone)
    uses the [functional_extensionality] axiom -- the same single
    axiom Coq-BB5 relies on. *)

From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

Definition ctape : Type := (list Sym * Sym * list Sym)%type.
Definition cconf : Type := (St * ctape)%type.

(** Read a list half-tape at an offset; blank beyond the end. *)
Definition nthb (l : list Sym) (n : nat) : Sym := nth n l S0.

Definition lift_side (l : list Sym) : nat -> Sym := fun n => nthb l n.

Definition lift_tape (ct : ctape) : Tape :=
  let '(l, h, r) := ct in mkTape (lift_side l) h (lift_side r).

Definition lift (c : cconf) : ExecState := (fst c, lift_tape (snd c)).

Definition c0 : cconf := (StA, ([], S0, [])).

Definition chd (l : list Sym) : Sym :=
  match l with [] => S0 | x :: _ => x end.

Definition ctl (l : list Sym) : list Sym :=
  match l with [] => [] | _ :: t => t end.

Definition ctape_move (d : Dir) (w : Sym) (ct : ctape) : ctape :=
  let '(l, h, r) := ct in
  match d with
  | DR => (w :: l, chd r, ctl r)
  | DL => (ctl l, chd l, w :: r)
  end.

Definition cstep (tm : TM) (c : cconf) : option cconf :=
  let (q, ct) := c in
  let '(l, h, r) := ct in
  match tm q h with
  | None => None
  | Some tr => Some (t_next tr, ctape_move (t_dir tr) (t_write tr) ct)
  end.

Fixpoint csteps (tm : TM) (n : nat) (c : cconf) : option cconf :=
  match n with
  | 0 => Some c
  | S m => match cstep tm c with
           | None => None
           | Some c' => csteps tm m c'
           end
  end.

(** ** [lift] commutation lemmas *)

Lemma lift_side_nil : lift_side [] = blank_side.
Proof.
  apply functional_extensionality; intro n.
  destruct n; reflexivity.
Qed.

Lemma lift_c0 : lift c0 = InitES.
Proof.
  unfold lift, InitES; simpl. rewrite lift_side_nil. reflexivity.
Qed.

Lemma lift_side_cons : forall w l, lift_side (w :: l) = push_side w (lift_side l).
Proof.
  intros; apply functional_extensionality; intro n.
  destruct n; reflexivity.
Qed.

Lemma lift_side_tl : forall l, lift_side (ctl l) = tail_side (lift_side l).
Proof.
  intros; apply functional_extensionality; intro n.
  destruct l; destruct n; reflexivity.
Qed.

Lemma lift_side_hd : forall l, chd l = lift_side l 0.
Proof. destruct l; reflexivity. Qed.

Lemma lift_move : forall d w ct,
  tape_move d w (lift_tape ct) = lift_tape (ctape_move d w ct).
Proof.
  intros d w [[l h] r]; destruct d; simpl;
    rewrite lift_side_tl, lift_side_cons, lift_side_hd; reflexivity.
Qed.

Lemma lift_state : forall c, fst (lift c) = fst c.
Proof. reflexivity. Qed.

Lemma cstep_lift : forall tm c c',
  cstep tm c = Some c' -> step tm (lift c) = Some (lift c').
Proof.
  intros tm [q [[l h] r]] c' H; simpl in H.
  destruct (tm q h) as [tr|] eqn:E; [|discriminate].
  injection H as <-.
  unfold step, lift; simpl. rewrite E.
  do 2 f_equal.
  destruct (t_dir tr); simpl;
    rewrite lift_side_tl, lift_side_cons, lift_side_hd; reflexivity.
Qed.

Lemma csteps_lift : forall tm n c c',
  csteps tm n c = Some c' -> stepn tm n (lift c) = Some (lift c').
Proof.
  induction n; intros c c' H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (cstep tm c) eqn:E; [|discriminate].
    cbn [stepn]. rewrite (cstep_lift _ _ _ E). auto.
Qed.

Lemma csteps_add : forall tm a b c,
  csteps tm (a + b) c =
  match csteps tm a c with
  | Some c' => csteps tm b c'
  | None => None
  end.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - destruct (cstep tm c); [apply IHa | reflexivity].
Qed.

Lemma csteps_prefix : forall tm a b c c',
  a <= b -> csteps tm b c = Some c' ->
  exists cm, csteps tm a c = Some cm /\ csteps tm (b - a) cm = Some c'.
Proof.
  intros tm a b c c' Hle H.
  replace b with (a + (b - a)) in H by lia.
  rewrite csteps_add in H.
  destruct (csteps tm a c) eqn:E; [eauto | discriminate].
Qed.

Lemma csteps_1 : forall tm c, csteps tm 1 c = cstep tm c.
Proof. intros; simpl. destruct (cstep tm c); reflexivity. Qed.

(** ** Decidable configuration equality (up to blank padding) *)

Fixpoint all_blank (l : list Sym) : bool :=
  match l with
  | [] => true
  | x :: t => sym_eqb x S0 && all_blank t
  end.

Fixpoint lpad_eqb (a b : list Sym) : bool :=
  match a, b with
  | [], _ => all_blank b
  | x :: a', [] => sym_eqb x S0 && lpad_eqb a' []
  | x :: a', y :: b' => sym_eqb x y && lpad_eqb a' b'
  end.

Lemma nthb_nil : forall n, nthb [] n = S0.
Proof. destruct n; reflexivity. Qed.

Lemma all_blank_nthb : forall l, all_blank l = true -> forall n, nthb l n = S0.
Proof.
  induction l as [|x l' IH]; intros H n.
  - apply nthb_nil.
  - simpl in H. apply andb_prop in H as [H1 H2].
    apply sym_eqb_spec in H1; subst.
    destruct n; [reflexivity | apply IH, H2].
Qed.

Lemma lpad_eqb_nthb : forall a b,
  lpad_eqb a b = true -> forall n, nthb a n = nthb b n.
Proof.
  induction a as [|x a' IH]; intros [|y b'] H n; simpl in H.
  - reflexivity.
  - rewrite (all_blank_nthb (y :: b') H n). apply nthb_nil.
  - apply andb_prop in H as [H1 H2].
    apply sym_eqb_spec in H1; subst.
    destruct n as [|m]; [reflexivity|].
    rewrite !nthb_nil.
    change (nthb a' m = S0).
    rewrite (IH [] H2 m). apply nthb_nil.
  - apply andb_prop in H as [H1 H2].
    apply sym_eqb_spec in H1; subst.
    destruct n as [|m]; [reflexivity | apply (IH _ H2 m)].
Qed.

Lemma lpad_eqb_lift : forall a b,
  lpad_eqb a b = true -> lift_side a = lift_side b.
Proof.
  intros a b H; apply functional_extensionality; intro n.
  apply (lpad_eqb_nthb _ _ H n).
Qed.

Definition ceqb (c1 c2 : cconf) : bool :=
  let '(q1, (l1, h1, r1)) := c1 in
  let '(q2, (l2, h2, r2)) := c2 in
  st_eqb q1 q2 && sym_eqb h1 h2 && lpad_eqb l1 l2 && lpad_eqb r1 r2.

Lemma ceqb_lift : forall c1 c2, ceqb c1 c2 = true -> lift c1 = lift c2.
Proof.
  intros [q1 [[l1 h1] r1]] [q2 [[l2 h2] r2]] H; simpl in H.
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hq Hh].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh; subst.
  unfold lift; simpl.
  rewrite (lpad_eqb_lift _ _ Hl), (lpad_eqb_lift _ _ Hr).
  reflexivity.
Qed.
