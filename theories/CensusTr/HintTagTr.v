(** Advisory winner tags for instruction-census checkers.
    Schema version 1: zero-based rung indices, exactly 38 valid tags.
    A tag carries no proof; consumers check the actual machine and fall
    back on an invalid or failed hint. *)
From Coq Require Import Arith Bool List PArith.
Import ListNotations.

Inductive TrHorizon := TrShort | TrFull.

Inductive TrWinner :=
| WNGram (index : nat)
| WRank (index : nat)
| WQHPlain (horizon : TrHorizon) (index : nat)
| WQHLex (horizon : TrHorizon) (index : nat)
| WQHRW (horizon : TrHorizon) (index : nat)
| WRW (index : nat).

Definition TrHintRow : Type := (positive * TrWinner)%type.
Definition tr_hint_schema_version : nat := 1.

Definition tr_winner_valid (w : TrWinner) : bool :=
  match w with
  | WNGram i | WRank i | WRW i => i <? 4
  | WQHPlain _ i => i <? 9
  | WQHLex _ i => i <? 3
  | WQHRW _ i => i <? 1
  end.

(** Wire codes preserve full ladder order: N, rank, short QH, full QH, RW.
    [None] rejects invalid constructor indices instead of aliasing a valid
    tag from the next family. *)
Definition tr_winner_encode (w : TrWinner) : option nat :=
  if tr_winner_valid w then
    Some (match w with
    | WNGram i => i
    | WRank i => 4 + i
    | WQHPlain TrShort i => 8 + i
    | WQHLex TrShort i => 17 + i
    | WQHRW TrShort i => 20 + i
    | WQHPlain TrFull i => 21 + i
    | WQHLex TrFull i => 30 + i
    | WQHRW TrFull i => 33 + i
    | WRW i => 34 + i
    end)
  else None.

(** Total serialization helper. 38 is an INVALID sentinel, never a hint.
    An offline parser must reject it, not silently skip the row. *)
Definition tr_winner_code (w : TrWinner) : nat :=
  match tr_winner_encode w with Some code => code | None => 38 end.

Definition tr_winner_decode (code : nat) : option TrWinner :=
  if code <? 4 then Some (WNGram code) else
  if code <? 8 then Some (WRank (code - 4)) else
  if code <? 17 then Some (WQHPlain TrShort (code - 8)) else
  if code <? 20 then Some (WQHLex TrShort (code - 17)) else
  if code <? 21 then Some (WQHRW TrShort (code - 20)) else
  if code <? 30 then Some (WQHPlain TrFull (code - 21)) else
  if code <? 33 then Some (WQHLex TrFull (code - 30)) else
  if code <? 34 then Some (WQHRW TrFull (code - 33)) else
  if code <? 38 then Some (WRW (code - 34)) else None.

Definition all_tr_winners : list TrWinner :=
  map WNGram (seq 0 4) ++ map WRank (seq 0 4) ++
  map (WQHPlain TrShort) (seq 0 9) ++
  map (WQHLex TrShort) (seq 0 3) ++ [WQHRW TrShort 0] ++
  map (WQHPlain TrFull) (seq 0 9) ++
  map (WQHLex TrFull) (seq 0 3) ++ [WQHRW TrFull 0] ++
  map WRW (seq 0 4).

Example tr_winner_count : length all_tr_winners = 38.
Proof. reflexivity. Qed.

Example tr_winner_codes : map tr_winner_code all_tr_winners = seq 0 38.
Proof. reflexivity. Qed.

Example tr_winner_roundtrips :
  map (fun w => tr_winner_decode (tr_winner_code w)) all_tr_winners =
  map (@Some TrWinner) all_tr_winners.
Proof. reflexivity. Qed.

Example tr_winner_reject_sentinel : tr_winner_decode 38 = None.
Proof. reflexivity. Qed.

Example tr_winner_reject_bad_index : tr_winner_encode (WNGram 4) = None.
Proof. reflexivity. Qed.
