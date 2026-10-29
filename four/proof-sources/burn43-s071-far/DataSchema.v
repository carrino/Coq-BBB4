From Coq Require Import List Bool PArith FSets.FMapPositive.
From BBB24Burn43S071FAR Require Import Sparse.
Import ListNotations.
Set Implicit Arguments.

Record h3row := Row { rw : positive; rq : bool; rr : positive }.
Record localout := Out { ow : positive; oq : bool; ob : bool }.
Record rawcert := Cert {
  words : PM.t (nat * nat);
  h3 : PM.t h3row;
  push : PM.t (PM.t positive);
  h2 : set;
  retl : set;
  pre3l : set;
  ret2 : adj;
  ret3 : adj;
  pre32 : adj;
  pre33 : adj
}.

Definition blankword : positive := 1%positive.
Definition startsummary : positive := 2%positive.
Definition slot (q : bool) (r : positive) : positive :=
  if q then xI r else xO r.
Definition unslot (a : positive) : bool * positive :=
  match a with xI r => (true,r) | xO r => (false,r)
  | xH => (false,startsummary) end.
Lemma unslot_slot q r : unslot (slot q r) = (q,r).
Proof. now destruct q. Qed.

Definition getrow (d : rawcert) (c : positive) : h3row :=
  match PM.find c (h3 d) with Some row => row
  | None => Row blankword false startsummary end.
Definition cok (d : rawcert) (c : positive) : bool :=
  match PM.find c (h3 d) with Some _ => true | None => false end.
Definition zflag (r : positive) : bool := Pos.eqb r startsummary.

Definition pushfind (d : rawcert) (w r : positive) : option positive :=
  match PM.find w (push d) with Some rs => PM.find r rs | None => None end.

Definition roweqb (a b : h3row) : bool :=
  Pos.eqb (rw a) (rw b) && Bool.eqb (rq a) (rq b) && Pos.eqb (rr a) (rr b).
Lemma roweqb_true a b : roweqb a b = true -> a = b.
Proof.
  destruct a as [w q r], b as [w' q' r']; unfold roweqb; simpl.
  repeat rewrite andb_true_iff; intros [[Hw Hq] Hr].
  apply Pos.eqb_eq in Hw; apply Bool.eqb_prop in Hq; apply Pos.eqb_eq in Hr.
  now subst.
Qed.

Definition localfun := positive -> bool -> bool -> bool -> bool -> option localout.
