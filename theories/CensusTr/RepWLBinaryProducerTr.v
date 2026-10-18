(** RW certificate production with binary rank and potential payloads.
    Rule-b potentials use Z.to_N. Search control, graph/SCC order, fuel,
    guards and measure order follow RepWLSearchTr. Soundness comes from
    checking the produced certificate; whole-producer equality is not assumed. *)
From Coq Require Import Arith Bool List NArith ZArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import RepWLSearchTr.
Import ListNotations.
Open Scope nat_scope.

Inductive rwcompN : Type :=
| RwRankN (phi : list (positive * N))
| RwMeasN (m : rwmeas) (K : nat) (phi : list (positive * N))
          (gate : list positive).

Definition rw_phiN_legacy (phi : list (positive * N)) : list (positive * nat) :=
  map (fun p => (fst p, N.to_nat (snd p))) phi.
Definition rwcompN_legacy (c : rwcompN) : rwcomp :=
  match c with
  | RwRankN phi => RwRankE (rw_phiN_legacy phi)
  | RwMeasN m K phi gate => RwMeasE m K (rw_phiN_legacy phi) gate
  end.

(** Direct binary version of the existing DAG rank computation. The fold,
    successor and maximum operations retain their original order. Rank values
    are computed once per component and shared by every assigned node. *)
Definition irank_get_binary_tr (r : PositiveMap.tree N) (v : positive) : N :=
  match PositiveMap.find v r with Some n => n | None => 0%N end.
Definition component_rank_binary_tr (g : IAdj) (c : list positive)
    (r : PositiveMap.tree N) : PositiveMap.tree N :=
  let cs := icset_of c in
  let rank := fold_left (fun n a =>
    fold_left (fun n b =>
      if PositiveSet.mem b cs then n
      else N.max n (N.succ (irank_get_binary_tr r b))) (iadj_get g a) n) c 0%N in
  fold_left (fun r' a => PositiveMap.add a rank r') c r.
Definition component_ranks_binary_tr (g : IAdj) (comps : list (list positive))
    : PositiveMap.tree N :=
  match comps with
  | [] | [_] => PositiveMap.empty N
  | _ => fold_left (fun r c => component_rank_binary_tr g c r)
      (rev comps) (PositiveMap.empty N)
  end.
Definition rank_certificate_binary_tr (arr : PositiveMap.tree rconf)
    (idxs : list positive) (g : IAdj) (comps : list (list positive))
    : list (positive * N) :=
  let ranks := component_ranks_binary_tr g comps in
  map (fun v => (rkey (iarr_get arr v), irank_get_binary_tr ranks v)) idxs.

Lemma rule_b_numeric_roundtrip : forall z,
  N.to_nat (Z.to_N z) = Z.to_nat z.
Proof. intro z. apply Z_N_nat. Qed.

Definition itry_rule_a_binary_tr (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (es : list (positive * positive)) (m : rwmeas)
  : option (rwcompN * IAdj) :=
  let dv := idvec tm m arr c in
  let ds := map (fun '(a, _) => idvec_get dv a) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (RwMeasN m 1 [] (map (fun i => rkey (iarr_get arr i)) c),
             idelete_intra g cset c
               (fun a _ => Z.ltb (idvec_get dv a) 0))
  else None.

Definition itry_rule_b_binary_tr (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (Kc : nat)
    (es : list (positive * positive)) (m : rwmeas) : option (rwcompN * IAdj) :=
  let dv := idvec tm m arr c in
  if i_bad_self dv (Z.of_nat Kc) es then None else
  match ibell_iter (S (length c)) dv (Z.of_nat Kc) es
                   (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => match PositiveMap.find v dist with
                                | Some x => x | None => 0%Z end) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v =>
                        (rkey (iarr_get arr v),
                         Z.to_N ((match PositiveMap.find v dist with
                                    | Some x => x | None => 0%Z end) - mn)%Z))
                     c in
      Some (RwMeasN m Kc phi (map (fun i => rkey (iarr_get arr i)) c),
            idelete_intra g cset c (fun _ _ => true))
  end.

Definition iprocess_scc_binary_tr (tm : TM) (arr : PositiveMap.tree rconf) (Kc : nat)
    (st : IAdj * list rwcompN * bool) (c : list positive)
  : IAdj * list rwcompN * bool :=
  let '(g, acc, prog) := st in
  let cset := icset_of c in
  let es := iintra_edges g cset c in
  match rfirst_some (itry_rule_a_binary_tr tm arr g cset c es) rmeasures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match rfirst_some (itry_rule_b_binary_tr tm arr g cset c Kc es) rmeasures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

Fixpoint iproc_rounds_binary_tr (fuel : nat) (tm : TM)
    (arr : PositiveMap.tree rconf) (Kc rfuel : nat)
    (idxs : list positive) (g : IAdj) (acc : list rwcompN)
  : option (list rwcompN) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := iscc_partition rfuel idxs g in
      let cyc := filter (iscc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (RwRankN (rank_certificate_binary_tr arr idxs g comps) :: acc))
      | _ =>
          let '(g', fresh, prog) :=
            fold_left (iprocess_scc_binary_tr tm arr Kc) cyc (g, [], false) in
          if prog then
            let rank := RwRankN (rank_certificate_binary_tr arr idxs g comps) in
            iproc_rounds_binary_tr f tm arr Kc rfuel idxs g' (fresh ++ rank :: acc)
          else None
      end
  end.
