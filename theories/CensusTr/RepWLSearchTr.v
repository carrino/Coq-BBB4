(** * Instruction RepWL search: rank the SCC DAG in one pass.

    RepWLSearch already computes source-first strongly connected components.
    Its rank search nevertheless repeatedly relaxes every edge, with unary
    component indices converted to positive map keys on each visit. Here we
    traverse components sink-first, compute each component's longest-path
    rank once, and store it directly at its nodes' positive indices. The
    acyclic final round uses the same computation on singleton components.

    This is an UNTRUSTED certificate producer. RepWLTr and RepWLMBTr still
    use their original verified checkers for the complete result, including
    every rank and every edge. No checker or soundness premise changes. *)
From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import RepWLSearch.
Import ListNotations.

Definition irank_get_tr (r : PositiveMap.tree nat) (v : positive) : nat :=
  match PositiveMap.find v r with Some n => n | None => 0 end.

Definition component_rank_tr (g : IAdj) (c : list positive)
    (r : PositiveMap.tree nat) : PositiveMap.tree nat :=
  let cs := icset_of c in
  let rank := fold_left (fun n a =>
    fold_left (fun n b =>
      if PositiveSet.mem b cs then n
      else Nat.max n (S (irank_get_tr r b))) (iadj_get g a) n) c 0 in
  fold_left (fun r' a => PositiveMap.add a rank r') c r.

Definition component_ranks_tr (g : IAdj) (comps : list (list positive))
    : PositiveMap.tree nat :=
  (* A single SCC has no outgoing condensation edges: every rank is zero.
     The empty map already represents this, including for a singleton sink. *)
  match comps with
  | [] | [_] => PositiveMap.empty nat
  | _ => fold_left (fun r c => component_rank_tr g c r)
           (rev comps) (PositiveMap.empty nat)
  end.

Definition rank_certificate_tr (arr : PositiveMap.tree rconf)
    (idxs : list positive) (g : IAdj) (comps : list (list positive))
    : list (positive * nat) :=
  let ranks := component_ranks_tr g comps in
  map (fun v => (rkey (iarr_get arr v), irank_get_tr ranks v)) idxs.

Fixpoint iproc_rounds_tr (fuel : nat) (tm : TM)
    (arr : PositiveMap.tree rconf) (Kc rfuel : nat)
    (idxs : list positive) (g : IAdj) (acc : list rwcomp)
  : option (list rwcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := iscc_partition rfuel idxs g in
      let cyc := filter (iscc_cyclic g) comps in
      let rank := RwRankE (rank_certificate_tr arr idxs g comps) in
      match cyc with
      | [] => Some (rev (rank :: acc))
      | _ =>
          let '(g', acc'', prog) :=
            fold_left (iprocess_scc tm arr Kc) cyc (g, rank :: acc, false) in
          if prog then iproc_rounds_tr f tm arr Kc rfuel idxs g' acc''
          else None
      end
  end.
