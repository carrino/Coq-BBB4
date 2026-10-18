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
From Coq Require Import Arith Bool List ZArith PArith.
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

(** The SCC's intra-edge list is independent of its measure.  Hoist it
    across all rule attempts; the wrappers retain exactly the shared
    producers' result, including the positive self-loop rejection. *)

Definition itry_rule_a_edges_tr (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (es : list (positive * positive)) (m : rwmeas)
  : option (rwcomp * IAdj) :=
  let dv := idvec tm m arr c in
  let ds := map (fun '(a, _) => idvec_get dv a) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (RwMeasE m 1 [] (map (fun i => rkey (iarr_get arr i)) c),
             idelete_intra g cset c
               (fun a _ => Z.ltb (idvec_get dv a) 0))
  else None.

Definition itry_rule_b_edges_tr (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (Kc : nat)
    (es : list (positive * positive)) (m : rwmeas) : option (rwcomp * IAdj) :=
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
                         Z.to_nat ((match PositiveMap.find v dist with
                                    | Some x => x | None => 0%Z end) - mn)%Z))
                     c in
      Some (RwMeasE m Kc phi (map (fun i => rkey (iarr_get arr i)) c),
            idelete_intra g cset c (fun _ _ => true))
  end.

Definition iprocess_scc_tr (tm : TM) (arr : PositiveMap.tree rconf) (Kc : nat)
    (st : IAdj * list rwcomp * bool) (c : list positive)
  : IAdj * list rwcomp * bool :=
  let '(g, acc, prog) := st in
  let cset := icset_of c in
  let es := iintra_edges g cset c in
  match rfirst_some (itry_rule_a_edges_tr tm arr g cset c es) rmeasures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match rfirst_some (itry_rule_b_edges_tr tm arr g cset c Kc es) rmeasures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

Lemma itry_rule_a_edges_tr_spec : forall tm arr g cset c m,
  itry_rule_a_edges_tr tm arr g cset c (iintra_edges g cset c) m =
  itry_rule_a tm arr g cset c m.
Proof. reflexivity. Qed.

Lemma itry_rule_b_edges_tr_spec : forall tm arr g cset c Kc m,
  itry_rule_b_edges_tr tm arr g cset c Kc (iintra_edges g cset c) m =
  itry_rule_b tm arr g cset c Kc m.
Proof. reflexivity. Qed.

Lemma iprocess_scc_tr_spec : forall tm arr Kc st c,
  iprocess_scc_tr tm arr Kc st c = iprocess_scc tm arr Kc st c.
Proof. intros tm arr Kc [[g acc] prog] c. reflexivity. Qed.

Lemma ifold_scc_reference_tr : forall tm arr Kc cs st,
  fold_left (iprocess_scc_tr tm arr Kc) cs st =
  fold_left (iprocess_scc tm arr Kc) cs st.
Proof.
  intros tm arr Kc cs. induction cs as [|c cs IH]; intros st.
  - reflexivity.
  - cbn [fold_left]. rewrite iprocess_scc_tr_spec. apply IH.
Qed.

Definition iscc_acc_append_tr (st : IAdj * list rwcomp * bool)
    (tail : list rwcomp) : IAdj * list rwcomp * bool :=
  let '(g, acc, prog) := st in (g, acc ++ tail, prog).

Lemma iprocess_scc_append_tr : forall tm arr Kc st tail c,
  iprocess_scc tm arr Kc (iscc_acc_append_tr st tail) c =
  iscc_acc_append_tr (iprocess_scc tm arr Kc st c) tail.
Proof.
  intros tm arr Kc [[g acc] prog] tail c.
  unfold iprocess_scc, iscc_acc_append_tr.
  destruct (rfirst_some (itry_rule_a tm arr g (icset_of c) c) rmeasures)
    as [[comp g']|]; [reflexivity|].
  destruct (rfirst_some (itry_rule_b tm arr g (icset_of c) c Kc) rmeasures)
    as [[comp g']|]; reflexivity.
Qed.

Lemma ifold_scc_append_tr : forall tm arr Kc cs st tail,
  fold_left (iprocess_scc tm arr Kc) cs (iscc_acc_append_tr st tail) =
  iscc_acc_append_tr (fold_left (iprocess_scc tm arr Kc) cs st) tail.
Proof.
  intros tm arr Kc cs. induction cs as [|c cs IH]; intros st tail.
  - reflexivity.
  - cbn [fold_left]. rewrite iprocess_scc_append_tr. apply IH.
Qed.

Fixpoint iproc_rounds_tr_reference (fuel : nat) (tm : TM)
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
          if prog then iproc_rounds_tr_reference f tm arr Kc rfuel idxs g' acc''
          else None
      end
  end.

(** A failed round discards every certificate.  First collect only the
    SCC components.  Construct the unchanged condensation rank after
    progress is known, preserving the exact component/accumulator order. *)
Fixpoint iproc_rounds_tr (fuel : nat) (tm : TM)
    (arr : PositiveMap.tree rconf) (Kc rfuel : nat)
    (idxs : list positive) (g : IAdj) (acc : list rwcomp)
  : option (list rwcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := iscc_partition rfuel idxs g in
      let cyc := filter (iscc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (RwRankE (rank_certificate_tr arr idxs g comps) :: acc))
      | _ =>
          let '(g', fresh, prog) :=
            fold_left (iprocess_scc_tr tm arr Kc) cyc (g, [], false) in
          if prog then
            let rank := RwRankE (rank_certificate_tr arr idxs g comps) in
            iproc_rounds_tr f tm arr Kc rfuel idxs g' (fresh ++ rank :: acc)
          else None
      end
  end.

Theorem iproc_rounds_tr_spec : forall fuel tm arr Kc rfuel idxs g acc,
  iproc_rounds_tr fuel tm arr Kc rfuel idxs g acc =
  iproc_rounds_tr_reference fuel tm arr Kc rfuel idxs g acc.
Proof.
  induction fuel as [|fuel IH]; intros tm arr Kc rfuel idxs g acc.
  - reflexivity.
  - cbn [iproc_rounds_tr iproc_rounds_tr_reference].
    set (comps := iscc_partition rfuel idxs g).
    destruct (filter (iscc_cyclic g) comps) as [|c cs]; [reflexivity|].
    rewrite ifold_scc_reference_tr.
    pose proof (ifold_scc_append_tr tm arr Kc (c :: cs) (g, [], false)
      (RwRankE (rank_certificate_tr arr idxs g comps) :: acc)) as E.
    change
      (fold_left (iprocess_scc tm arr Kc) (c :: cs)
         (g, RwRankE (rank_certificate_tr arr idxs g comps) :: acc, false) =
       iscc_acc_append_tr
         (fold_left (iprocess_scc tm arr Kc) (c :: cs) (g, [], false))
         (RwRankE (rank_certificate_tr arr idxs g comps) :: acc)) in E.
    rewrite E.
    destruct (fold_left (iprocess_scc tm arr Kc) (c :: cs) (g, [], false))
      as [[g' fresh] prog].
    cbn [iscc_acc_append_tr].
    destruct prog; [apply IH|reflexivity].
Qed.
