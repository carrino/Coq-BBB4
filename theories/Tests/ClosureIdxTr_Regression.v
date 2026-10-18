(** Regression checks for the instruction-level interned validator. *)
From Coq Require Import Arith List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc.
From BBB4.Checkers Require Import ClosureIdxTr.
Import ListNotations.

Definition idxtr_test_tm : TM := fun _ _ => None.
Definition idxtr_test_enc (n : nat) : positive := Pos.of_succ_nat n.
Definition idxtr_test_instr (n : nat) : Instr :=
  if n =? 0 then (StA, S0) else (StB, S1).
Definition idxtr_test_succs (n : nat) : option (list nat) :=
  Some [if n =? 0 then 1 else if n =? 1 then 2 else 0].
Definition idxtr_test_cert (_ : Instr) : list (epres nat) :=
  [ERank nat (PositiveMap.add (idxtr_test_enc 1) 1 (PositiveMap.empty nat))].
Definition idxtr_bad_cert (_ : Instr) : list (epres nat) :=
  [ERank nat (PositiveMap.empty nat)].

(* A three-node cycle: the sole A instruction and both B instructions recur.
   Avoiding A leaves an edge from node 1 (rank 1) to node 2 (rank 0). *)
Example idxtr_accepts_valid_rank :
  lex_check_idx idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 10 0 idxtr_test_cert = true.
Proof. native_compute. reflexivity. Qed.

Example idxtr_rejects_bad_rank :
  lex_check_idx idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 10 0 idxtr_bad_cert = false.
Proof. native_compute. reflexivity. Qed.

Example idxtr_rejects_missing_certificate :
  lex_check_idx idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 10 0 (fun _ => []) = false.
Proof. native_compute. reflexivity. Qed.

(* Node 1 has a successor outside this proposed pool. *)
Example idxtr_rejects_escaped_edge :
  lex_check_idx_pool idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 0 [0; 1] idxtr_test_cert = false.
Proof. native_compute. reflexivity. Qed.

Example idxtr_rejects_missing_root :
  lex_check_idx_pool idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 3 [0; 1; 2] idxtr_test_cert = false.
Proof. native_compute. reflexivity. Qed.

Example idxtr_rejects_exhausted_search :
  lex_check_idx idxtr_test_tm nat idxtr_test_enc idxtr_test_instr
    idxtr_test_succs 0 1 0 idxtr_test_cert = false.
Proof. native_compute. reflexivity. Qed.

Print Assumptions lex_check_idx_spec.
Print Assumptions lex_check_idx_pool_spec.
Print Assumptions idxtr_accepts_valid_rank.
