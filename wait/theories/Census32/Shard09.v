(** First-transition shard 9/12; covers every completion of five cells. *)
From Coq Require Import List.
From BBBWait Require Import Census Check32.

Lemma state32_shard09 :
  check32_head state32_check (nth 9 choices32 None) = true.
Proof. native_compute; reflexivity. Qed.

Lemma instr32_shard09 :
  check32_head instr32_check (nth 9 choices32 None) = true.
Proof. native_compute; reflexivity. Qed.
