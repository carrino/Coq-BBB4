(** Total ordinary-inductive-byte decoder. This is arbitrary certificate data:
    the unchanged unit_check still verifies every decoded witness. No theorem
    assumes that this decoder matches an external encoding specification. *)
From Coq Require Import List NArith Strings.Byte.
Import ListNotations.
Local Open Scope N_scope.

Fixpoint decode_acc (bytes : list byte) (partial place : N)
  {struct bytes} : list N :=
  match bytes with
  | [] => []
  | head :: tail =>
      let value := Byte.to_N head in
      let next := partial + (value mod 128) * place in
      if value <? 128
      then next :: decode_acc tail 0 1
      else decode_acc tail next (place * 128)
  end.

Definition decode_words (bytes : list byte) : list N :=
  decode_acc bytes 0 1.
