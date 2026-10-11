(** * Data-only frontier and unit computations for the instruction census.

    RunTr_Split proves soundness for these exact definitions. The walk
    units can evaluate them without importing any proven-tier boards. *)
From Coq Require Import Arith Bool List.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Export RunTr_Compute.
Import ListNotations.

Definition qnodes (q : SearchQueue) : list TNF_Node := fst q ++ snd q.

Definition FRONTIER_LEVELS_TR : nat := 3.

Definition frontier_tr : SearchQueue :=
  SearchQueue_levels decider_tr_fast FRONTIER_LEVELS_TR q_0_tr.

Definition frontier_nodes_tr : list TNF_Node := qnodes frontier_tr.

(** The original successor-round budget; exhaustion makes further
    iterations no-ops. *)
Definition ITER_TR : nat := 4096.

Definition queue_empty_b (q : SearchQueue) : bool :=
  match q with ([], []) => true | _ => false end.

(** Check the nodes whose indices belong to unit [i] modulo [N]. *)
Fixpoint unit_ok (N i j : nat) (l : list TNF_Node) : bool :=
  match l with
  | [] => true
  | h :: t =>
      (if Nat.eqb (j mod N) i
       then queue_empty_b (Nat.iter ITER_TR q_suc_tr ([h], []))
       else true)
      && unit_ok N i (S j) t
  end.
