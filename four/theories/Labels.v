From Coq Require Import List.
From BBB24 Require Import Statement StatementTr CTape Bounds.
Import ListNotations.

Definition labels {A} (ai : A -> Instr) (Sl : list A) : list cconf :=
  map (fun a => (fst (ai a), ([],snd (ai a),[]))) Sl.

Lemma labels_instr : forall A (ai : A -> Instr) Sl tg,
  tail_instrs (labels ai Sl) tg = existsb (fun a => instr_eqb (ai a) tg) Sl.
Proof.
  intros A ai Sl tg. unfold tail_instrs, labels.
  induction Sl as [|a Sl IH]; cbn [map existsb]; [reflexivity|].
  rewrite IH. destruct (ai a). reflexivity.
Qed.
