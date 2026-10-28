(** Positive-weight self-loops make every Bellman-Ford pass change.
    Reject these impossible potential constraints before repeated relaxation. *)
From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
Import ListNotations.
Section GenericSelfLoop.
Variable A : Type.
Variable key : A -> positive.
Variable weight : A -> A -> Z.
Definition self_get (d : PositiveMap.tree Z) (a : A) : Z :=
  match PositiveMap.find (key a) d with Some v => v | None => 0%Z end.
Definition self_relax (st : PositiveMap.tree Z * bool) (e : A * A) :=
  let '(dist,ch) := st in let '(a,b) := e in
  let w := weight a b in
  let da := self_get dist a in let db := self_get dist b in
  if Z.ltb (da - w)%Z db
  then (PositiveMap.add (key b) ((da-w)%Z) dist, true)
  else (dist,ch).
Fixpoint bad_self (es : list (A*A)) : bool :=
  match es with
  | [] => false
  | (a,b)::rest =>
      if Pos.eqb (key a) (key b)
      then if Z.ltb 0 (weight a b) then true else bad_self rest
      else bad_self rest
  end.
Lemma self_pass_changed : forall es dist,
  snd (fold_left self_relax es (dist,true)) = true.
Proof.
  induction es as [|[a b] es IH]; intros dist; cbn [fold_left self_relax]; [reflexivity|].
  destruct (Z.ltb (self_get dist a - weight a b) (self_get dist b)); apply IH.
Qed.
Lemma self_pass_bad : forall es, bad_self es = true -> forall dist ch,
  snd (fold_left self_relax es (dist,ch)) = true.
Proof.
  induction es as [|[a b] es IH]; intros H dist ch; [discriminate|].
  cbn [bad_self] in H. cbn [fold_left].
  destruct (Pos.eqb (key a) (key b)) eqn:Ek.
  - destruct (Z.ltb 0 (weight a b)) eqn:Ew.
    + apply Pos.eqb_eq in Ek. apply Z.ltb_lt in Ew.
      assert (Eget : self_get dist a = self_get dist b).
      { unfold self_get. rewrite Ek. reflexivity. }
      assert (Elt : Z.ltb (self_get dist a - weight a b) (self_get dist b) = true).
      { apply Z.ltb_lt. rewrite Eget. lia. }
      cbn [self_relax]. rewrite Elt. apply self_pass_changed.
    + destruct (self_relax (dist,ch) (a,b)) as [d' c']. apply IH; exact H.
  - destruct (self_relax (dist,ch) (a,b)) as [d' c']. apply IH; exact H.
Qed.
End GenericSelfLoop.
