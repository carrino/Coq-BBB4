(** Compare the new certificate producer with the original relaxation
    algorithm on every three-vertex graph and every vertex ordering.
    Include self loops, cycles, disconnected graphs and a larger mixed DAG.
    These are finite regression tests, not a universal equivalence claim;
    production certificates remain subject to the original verified checker. *)
From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import RepWLSearchTr.
Import ListNotations.

Definition vertices3 := [1%positive; 2%positive; 3%positive].
Definition vertex_orders3 :=
  [[1; 2; 3]; [1; 3; 2]; [2; 1; 3];
   [2; 3; 1]; [3; 1; 2]; [3; 2; 1]]%positive.

Definition graph3 (bits : nat) : IAdj :=
  fold_left (fun g a => PositiveMap.add a
    (filter (fun b => Nat.testbit bits
      ((Pos.to_nat a - 1) * 3 + Pos.to_nat b - 1)) vertices3)
    g) vertices3 (PositiveMap.empty _).

Definition condensation_reference (idxs : list positive)
    (g : IAdj) (cs : list (list positive)) :=
  let cid := icid_map cs in
  let rk := icrank_iter (S (length cs)) idxs g cid (PositiveMap.empty nat) in
  map (fun v => rcrk_get rk (icid_get cid v)) idxs.

Definition list_nat_eqb (xs ys : list nat) :=
  (length xs =? length ys) &&
  forallb (fun p => fst p =? snd p) (combine xs ys).

Definition ranks_agree (idxs : list positive) (g : IAdj) : bool :=
  let cs := iscc_partition (S (length idxs * 8 + 8)) idxs g in
  let fast := map (irank_get_tr (component_ranks_tr g cs)) idxs in
  list_nat_eqb (condensation_reference idxs g cs) fast &&
  if existsb (iscc_cyclic g) cs then true else
    let rk := inrank_iter (S (length idxs)) idxs g (PositiveMap.empty nat) in
    list_nat_eqb (map (irank_get_tr rk) idxs) fast.

Definition all_graphs3 := forallb (fun idxs =>
  forallb (fun bits => ranks_agree idxs (graph3 bits)) (seq 0 512))
  vertex_orders3.

Example all_three_vertex_graphs_vm : all_graphs3 = true.
Proof. vm_compute. reflexivity. Qed.

Example all_three_vertex_graphs_native : all_graphs3 = true.
Proof. native_cast_no_check (eq_refl true). Qed.

Definition mixed_graph : IAdj := fold_left
  (fun g row => PositiveMap.add (fst row) (snd row) g)
  [(1, [2]); (2, [1; 3; 4]); (3, [4]); (4, [5]);
   (5, [4; 6]); (6, []); (7, [7]); (8, [])]%positive
  (PositiveMap.empty _).

Example mixed_components :
  ranks_agree [1; 2; 3; 4; 5; 6; 7; 8]%positive mixed_graph = true /\
  ranks_agree [8; 7; 6; 5; 4; 3; 2; 1]%positive mixed_graph = true.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions all_three_vertex_graphs_vm.
Print Assumptions all_three_vertex_graphs_native.
Print Assumptions mixed_components.
