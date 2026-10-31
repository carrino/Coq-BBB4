From Coq Require Import List.
From BBB24 Require Import Statement StatementTr CTape.
Definition cinstr (c:cconf) : Instr := (fst c, let '(_,h,_) := snd c in h).
Lemma cinstr_lift : forall c, instr_of (lift c)=cinstr c.
Proof. intros [q [[l h] r]]; reflexivity. Qed.
