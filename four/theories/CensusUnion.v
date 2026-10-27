(** Combine separately audited closeout boards without re-running a census. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Closeout.
Import ListNotations.

Theorem boards_sound : forall bs bi boards,
  Forall (BoardSound bs bi) boards -> BoardSound bs bi (concat boards).
Proof.
  intros bs bi boards H family Hin tm Hle.
  apply in_concat in Hin as (board & Hb & Hin).
  apply Forall_forall with (x:=board) in H; [|exact Hb].
  exact (H family Hin tm Hle).
Qed.

Definition BoardPending xs board := forall family, In family board -> Pending xs family.

Theorem boards_pending : forall xs boards,
  Forall (BoardPending xs) boards -> BoardPending xs (concat boards).
Proof.
  intros xs boards H family Hin.
  apply in_concat in Hin as (board & Hb & Hin).
  apply Forall_forall with (x:=board) in H; [|exact Hb].
  exact (H family Hin).
Qed.

Print Assumptions boards_sound.
Print Assumptions boards_pending.
