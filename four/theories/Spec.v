(** Public statement surface for two states and four symbols.
    All eight table cells are unrestricted; undefined transitions halt.
    The score is the last configuration index plus one. *)
From Coq Require Import NArith.
From BBB24 Require Import Statement StatementTr.

Definition champion : TM := fun q s => Some
  (match q,s with
  | StA,S0 => mkTrans S1 DR StB | StA,S1 => mkTrans S2 DL StA
  | StA,S2 => mkTrans S1 DR StA | StA,S3 => mkTrans S1 DL StB
  | StB,S0 => mkTrans S0 DL StB | StB,S1 => mkTrans S2 DR StB
  | StB,S2 => mkTrans S3 DR StB | StB,S3 => mkTrans S1 DL StA
  end).

Definition scoreN : N := 205770076433044242247860%N.
Definition previousN : N := 205770076433044242247859%N.
Definition score : nat := N.to_nat scoreN.
Definition previous_index : nat := N.to_nat previousN.
Definition AttainsSt tm B := exists q s, QuietAfter tm q s /\ S s = B.
Definition AttainsTr tm B := exists tg s, QuietAfterTr tm tg s /\ S s = B.
Definition QHBound B tm := forall q s, QuietAfter tm q s -> S s <= B.
Definition QHBoundTr B tm := forall tg s, QuietAfterTr tm tg s -> S s <= B.
Definition BBB24_state_lower_bound B := exists tm, AttainsSt tm B.
Definition BBB24_instruction_lower_bound B := exists tm, AttainsTr tm B.
