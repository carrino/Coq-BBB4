(** First-transition shard 10/12; covers every completion of five cells. *)
From Coq Require Import List.
From BBBWait Require Import Census23 Check23.

Lemma state23_shard10 :
  check23_head state23_check (nth 10 choices23 None) = true.
Proof. native_compute; reflexivity. Qed.

Lemma instr23_shard10 :
  check23_head instr23_check (nth 10 choices23 None) = true.
Proof. native_compute; reflexivity. Qed.
