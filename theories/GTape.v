(** * GTape: guarded (walled) computable configurations.

    The translated-cycler induction needs runs that provably depend
    only on a bounded window of the left half-tape.  A guarded
    configuration reuses [cconf], but its left list is treated as a
    WALL: [gstep] fails (returns [None]) if the head would move left
    past the end of the list, instead of materializing a blank.  The
    right list keeps the ordinary blank-materializing semantics.

    A guarded configuration therefore stands for a *family* of
    abstract configurations: one for every "rest" [rho] of the left
    half-tape below the wall ([glift], [lift_wall]).  The payoff is
    [gsteps_lift]: a successful guarded run lifts to an abstract run
    for EVERY rest simultaneously -- the run never looked below the
    wall, so the rest passes through untouched (with its offset
    unchanged, since pops and pushes at the top of the wall list
    keep the wall bottom fixed).

    [gmatch g1 g2] then says g2 is g1 again up to a deeper rest:
    same state and head, g2's left list extends g1's ([lprefix_eqb],
    so g2's wall is at least as deep and agrees on all of g1's
    depth), and the right lists denote the same half-tape
    ([lpad_eqb]).  [gmatch_lift] turns this into: every abstract
    instance of g2 is an abstract instance of g1 -- the step that
    closes the translated-cycle induction. *)

From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** Guarded stepping *)

Definition gstep (tm : TM) (g : cconf) : option cconf :=
  let (q, t) := g in
  let '(l, h, r) := t in
  match tm q h with
  | None => None
  | Some tr =>
      match t_dir tr with
      | DR => Some (t_next tr, (t_write tr :: l, chd r, ctl r))
      | DL => match l with
              | [] => None (* the wall *)
              | x :: l' => Some (t_next tr, (l', x, t_write tr :: r))
              end
      end
  end.

Fixpoint gsteps (tm : TM) (n : nat) (g : cconf) : option cconf :=
  match n with
  | 0 => Some g
  | S m => match gstep tm g with
           | None => None
           | Some g' => gsteps tm m g'
           end
  end.

Lemma gsteps_add : forall tm a b g,
  gsteps tm (a + b) g =
  match gsteps tm a g with
  | Some g' => gsteps tm b g'
  | None => None
  end.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - destruct (gstep tm g); [apply IHa | reflexivity].
Qed.

Lemma gsteps_prefix : forall tm a b g g',
  a <= b -> gsteps tm b g = Some g' ->
  exists gm, gsteps tm a g = Some gm /\ gsteps tm (b - a) gm = Some g'.
Proof.
  intros tm a b g g' Hle H.
  replace b with (a + (b - a)) in H by lia.
  rewrite gsteps_add in H.
  destruct (gsteps tm a g) eqn:E; [eauto | discriminate].
Qed.

(** ** Denotation with an arbitrary rest below the wall *)

Definition lift_wall (l : list Sym) (rho : nat -> Sym) : nat -> Sym :=
  fun n => if n <? length l then nthb l n else rho (n - length l).

Definition glift (rho : nat -> Sym) (g : cconf) : ExecState :=
  (fst g, let '(l, h, r) := snd g in
          mkTape (lift_wall l rho) h (lift_side r)).

Lemma glift_state : forall rho g, fst (glift rho g) = fst g.
Proof. reflexivity. Qed.

Lemma glift_blank : forall g, glift blank_side g = lift g.
Proof.
  intros [q [[l h] r]]; unfold glift, lift; simpl.
  do 2 f_equal.
  apply functional_extensionality; intro n.
  unfold lift_wall, lift_side, blank_side.
  destruct (n <? length l) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E.
  symmetry. apply nth_overflow; assumption.
Qed.

Lemma lift_wall_cons : forall w l rho,
  lift_wall (w :: l) rho = push_side w (lift_wall l rho).
Proof.
  intros; apply functional_extensionality; intro n.
  destruct n; reflexivity.
Qed.

Lemma gstep_lift : forall tm g g' rho,
  gstep tm g = Some g' -> step tm (glift rho g) = Some (glift rho g').
Proof.
  intros tm [q [[l h] r]] g' rho H; simpl in H.
  destruct (tm q h) as [tr|] eqn:E; [|discriminate].
  destruct (t_dir tr) eqn:Ed.
  - (* left move: pop a wall cell *)
    destruct l as [|x l']; [discriminate|].
    injection H as <-.
    unfold step, glift; simpl. rewrite E, Ed.
    do 2 f_equal.
    rewrite lift_side_cons. reflexivity.
  - (* right move: push onto the wall list *)
    injection H as <-.
    unfold step, glift; simpl. rewrite E, Ed.
    do 2 f_equal.
    rewrite lift_wall_cons, lift_side_hd, lift_side_tl. reflexivity.
Qed.

Lemma gsteps_lift : forall tm n g g' rho,
  gsteps tm n g = Some g' -> stepn tm n (glift rho g) = Some (glift rho g').
Proof.
  induction n; intros g g' rho H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (gstep tm g) eqn:E; [|discriminate].
    cbn [stepn]. rewrite (gstep_lift _ _ _ rho E). auto.
Qed.

(** ** Exact prefixes and padded windows *)

Fixpoint lprefix_eqb (a b : list Sym) : bool :=
  match a, b with
  | [], _ => true
  | _ :: _, [] => false
  | x :: a', y :: b' => sym_eqb x y && lprefix_eqb a' b'
  end.

Lemma lprefix_eqb_len : forall a b,
  lprefix_eqb a b = true -> length a <= length b.
Proof.
  induction a; intros [|y b'] H; simpl in *; try lia; try discriminate.
  apply andb_prop in H as [_ H2].
  specialize (IHa _ H2). lia.
Qed.

Lemma lprefix_eqb_nthb : forall a b n,
  lprefix_eqb a b = true -> n < length a -> nthb a n = nthb b n.
Proof.
  induction a as [|x a' IH]; intros [|y b'] n H Hn;
    simpl in *; try lia; try discriminate.
  apply andb_prop in H as [H1 H2].
  apply sym_eqb_spec in H1; subst.
  destruct n; [reflexivity|].
  change (nthb a' n = nthb b' n). apply IH; [assumption | lia].
Qed.

(** The first [W] cells of [l], blank-padded to length exactly [W]. *)
Fixpoint firstn_pad (W : nat) (l : list Sym) : list Sym :=
  match W with
  | 0 => []
  | S W' => match l with
            | [] => S0 :: firstn_pad W' []
            | x :: l' => x :: firstn_pad W' l'
            end
  end.

Lemma firstn_pad_length : forall W l, length (firstn_pad W l) = W.
Proof.
  induction W; intros [|x l']; simpl; auto.
Qed.

Lemma firstn_pad_nthb : forall W l n,
  n < W -> nthb (firstn_pad W l) n = nthb l n.
Proof.
  induction W; intros l n Hn; [lia|].
  destruct l as [|x l']; destruct n; simpl; try reflexivity.
  - change (nthb (firstn_pad W []) n = nthb [] (S n)).
    rewrite IHW by lia. rewrite !nthb_nil. reflexivity.
  - change (nthb (firstn_pad W l') n = nthb l' n). apply IHW; lia.
Qed.

(** Truncating a known left half-tape at depth [W] loses nothing:
    the tail becomes the rest. *)
Lemma lift_side_wall : forall W l,
  lift_side l = lift_wall (firstn_pad W l) (fun n => nthb l (n + W)).
Proof.
  intros; apply functional_extensionality; intro n.
  unfold lift_wall. rewrite firstn_pad_length.
  destruct (n <? W) eqn:E.
  - apply Nat.ltb_lt in E. symmetry. apply firstn_pad_nthb; assumption.
  - apply Nat.ltb_ge in E. unfold lift_side. f_equal. lia.
Qed.

(** ** Recurrence up to a deeper rest *)

Definition gmatch (g1 g2 : cconf) : bool :=
  let '(q1, (l1, h1, r1)) := g1 in
  let '(q2, (l2, h2, r2)) := g2 in
  st_eqb q1 q2 && sym_eqb h1 h2 && lprefix_eqb l1 l2 && lpad_eqb r2 r1.

Lemma gmatch_lift : forall g1 g2,
  gmatch g1 g2 = true ->
  forall rho, exists rho', glift rho g2 = glift rho' g1.
Proof.
  intros [q1 [[l1 h1] r1]] [q2 [[l2 h2] r2]] H rho; simpl in H.
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hq Hh].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh; subst.
  exists (fun n => lift_wall l2 rho (n + length l1)).
  unfold glift; simpl.
  do 2 f_equal.
  - apply functional_extensionality; intro n.
    pose proof (lprefix_eqb_len _ _ Hl) as Hlen.
    transitivity (if n <? length l1
                  then nthb l1 n
                  else lift_wall l2 rho (n - length l1 + length l1)).
    + destruct (n <? length l1) eqn:E1.
      * apply Nat.ltb_lt in E1.
        unfold lift_wall.
        assert (E2 : n <? length l2 = true) by (apply Nat.ltb_lt; lia).
        rewrite E2. symmetry. apply lprefix_eqb_nthb; assumption.
      * apply Nat.ltb_ge in E1.
        replace (n - length l1 + length l1) with n by lia.
        reflexivity.
    + unfold lift_wall at 2. reflexivity.
  - apply lpad_eqb_lift; assumption.
Qed.
