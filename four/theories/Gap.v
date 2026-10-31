(** Directional configurations: the head scans the first cell of the side
    it faces. Both lists are nearest-first, with implicit blank padding. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
From BBB24 Require Import Statement CTape.
Import ListNotations.

Definition leftward q l r : ExecState := lift (q, (ctl l, chd l, r)).
Definition rightward q l r : ExecState := lift (q, (l, chd r, ctl r)).
Definition gap q d l r := match d with DL => leftward q l r | DR => rightward q l r end.
Definition Runs tm n a b := stepn tm n a = Some b.
Lemma runs_zero : forall tm a, Runs tm 0 a a.
Proof. reflexivity. Qed.
Lemma runs_add : forall tm n m a b c,
  Runs tm n a b -> Runs tm m b c -> Runs tm (n+m) a c.
Proof. intros tm n m a b c H H'; unfold Runs in *; now rewrite stepn_add,H. Qed.
Lemma runs_one : forall tm a b, step tm a = Some b -> Runs tm 1 a b.
Proof. intros; unfold Runs; cbn; now rewrite H. Qed.

Lemma left_step : forall tm q s w d p l r,
  tm q s = Some (mkTrans w d p) ->
  Runs tm 1 (leftward q (s::l) r)
    (match d with DL => leftward p l (w::r) | DR => rightward p (w::l) r end).
Proof.
  intros; destruct d; apply runs_one; apply cstep_lift;
    cbn [cstep ctape_move ctl chd]; rewrite H; reflexivity.
Qed.
Lemma right_step : forall tm q s w d p l r,
  tm q s = Some (mkTrans w d p) ->
  Runs tm 1 (rightward q l (s::r))
    (match d with DL => leftward p l (w::r) | DR => rightward p (w::l) r end).
Proof.
  intros; destruct d; apply runs_one; apply cstep_lift;
    cbn [cstep ctape_move ctl chd]; rewrite H; reflexivity.
Qed.

Lemma repeat_snoc : forall (w:Sym) n r,
  repeat w n ++ w::r = w::(repeat w n ++ r).
Proof. intros w n; induction n; intros; cbn; [reflexivity|now rewrite IHn]. Qed.

Lemma chain_left : forall tm q s w n l r,
  tm q s = Some (mkTrans w DL q) ->
  Runs tm n (leftward q (repeat s n ++ l) r)
    (leftward q l (repeat w n ++ r)).
Proof.
  intros tm q s w n; induction n as [|n IH]; intros l r H; [apply runs_zero|].
  cbn [repeat app]. replace (S n) with (1+n) by lia.
  eapply runs_add; [apply left_step; exact H|].
  rewrite <- (repeat_snoc w n r).
  apply IH; exact H.
Qed.
Lemma chain_right : forall tm q s w n l r,
  tm q s = Some (mkTrans w DR q) ->
  Runs tm n (rightward q l (repeat s n ++ r))
    (rightward q (repeat w n ++ l) r).
Proof.
  intros tm q s w n; induction n as [|n IH]; intros l r H; [apply runs_zero|].
  cbn [repeat app]. replace (S n) with (1+n) by lia.
  eapply runs_add; [apply right_step; exact H|].
  rewrite <- (repeat_snoc w n l).
  apply IH; exact H.
Qed.

Lemma lift_side_pad_zero : forall l, lift_side (l ++ [S0]) = lift_side l.
Proof.
  induction l as [|s l IH].
  - change (lift_side [S0] = lift_side []).
    rewrite lift_side_cons, !lift_side_nil.
    apply functional_extensionality; intros [|n]; reflexivity.
  - cbn [app]. rewrite !lift_side_cons, IH. reflexivity.
Qed.
Lemma leftward_pad_right : forall q l r,
  leftward q l (r ++ [S0]) = leftward q l r.
Proof. intros; unfold leftward,lift,lift_tape; cbn; now rewrite lift_side_pad_zero. Qed.

Lemma gap_sides : forall q d l l' r r',
  lift_side l = lift_side l' -> lift_side r = lift_side r' ->
  gap q d l r = gap q d l' r'.
Proof.
  intros q d l l' r r' Hl Hr. destruct d;
    unfold gap,leftward,rightward,lift,lift_tape; cbn;
    rewrite !lift_side_tl, !lift_side_hd, Hl,Hr; reflexivity.
Qed.
Lemma lift_side_app_ext : forall p l r,
  lift_side l = lift_side r -> lift_side (p++l) = lift_side (p++r).
Proof.
  induction p; intros; cbn; [assumption|].
  rewrite !lift_side_cons. now rewrite (IHp l r H).
Qed.
Lemma lift_repeat_blank : forall n, lift_side (repeat S0 n) = blank_side.
Proof.
  induction n; [apply lift_side_nil|]. cbn [repeat]. rewrite lift_side_cons,IHn.
  apply functional_extensionality; intros [|k]; reflexivity.
Qed.
