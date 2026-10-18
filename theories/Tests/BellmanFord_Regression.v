(** Positive-weight self loops are impossible; zero and negative weights
    must continue to admit Bellman-Ford certificates. *)
From Coq Require Import List Bool ZArith PArith FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram RepWL.
From BBB4.Census Require Import BellmanFord RankSearch RepWLSearch.
Import ListNotations.

Example positive_self_rejected :
  bad_self positive (fun x => x) (fun _ _ => 1%Z) [(1%positive,1%positive)] = true.
Proof. reflexivity. Qed.
Example zero_self_allowed :
  bad_self positive (fun x => x) (fun _ _ => 0%Z) [(1%positive,1%positive)] = false.
Proof. reflexivity. Qed.
Example negative_self_allowed :
  bad_self positive (fun x => x) (fun _ _ => (-1)%Z) [(1%positive,1%positive)] = false.
Proof. reflexivity. Qed.
Example non_self_edge_allowed :
  bad_self positive (fun x => x) (fun _ _ => 1%Z) [(1%positive,2%positive)] = false.
Proof. reflexivity. Qed.

Definition erase_tm : TM := fun _ _ => Some (mkTrans S0 DR StA).
Definition one : cconf := (StA, ([],S1,[])).
Definition ng_graph := adj_set (PositiveMap.empty _) one [one].
Definition ng_vertices := cset_of [one].
Definition has_some {A : Type} (x : option A) := match x with Some _ => true | None => false end.

Example ng_zero_weight_keeps_certificate :
  has_some (try_rule_b erase_tm ng_graph ng_vertices [one] 1 MAll) = true.
Proof. vm_compute. reflexivity. Qed.
Example ng_negative_weight_keeps_certificate :
  has_some (try_rule_b erase_tm ng_graph ng_vertices [one] 2 MAll) = true.
Proof. vm_compute. reflexivity. Qed.
Example ng_positive_weight_rejects :
  has_some (try_rule_b erase_tm ng_graph ng_vertices [one] 0 MAll) = false.
Proof. vm_compute. reflexivity. Qed.

Definition rw_array := PositiveMap.add 1%positive (rw_seed 2 2 one) (PositiveMap.empty _).
Definition rw_graph := PositiveMap.add 1%positive [1%positive] (PositiveMap.empty _).
Definition rw_vertices := icset_of [1%positive].
Example rw_zero_weight_keeps_certificate :
  has_some (itry_rule_b erase_tm rw_array rw_graph rw_vertices [1%positive] 1 RwNA) = true.
Proof. vm_compute. reflexivity. Qed.
Example rw_negative_weight_keeps_certificate :
  has_some (itry_rule_b erase_tm rw_array rw_graph rw_vertices [1%positive] 2 RwNA) = true.
Proof. vm_compute. reflexivity. Qed.
Example rw_positive_weight_rejects :
  has_some (itry_rule_b erase_tm rw_array rw_graph rw_vertices [1%positive] 0 RwNA) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions try_rule_b_spec.
Print Assumptions itry_rule_b_spec.
Print Assumptions ng_zero_weight_keeps_certificate.
Print Assumptions rw_zero_weight_keeps_certificate.
