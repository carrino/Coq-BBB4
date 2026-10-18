(** Exact precomputation for the transition rank producer.
    Graph order, relaxation fuel, self-loop rejection and certificate output
    are preserved. No checker or soundness premise is changed. *)
From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import RankSearch BellmanFord.
From BBB4.CensusTr Require Import BellmanFordWeightedTr.
Import ListNotations.

Definition ng_bell_edges_tr (tm : TM) (m : ngmeas) (Kc : Z)
    (es : list (cconf * cconf)) : list weighted_edge_tr :=
  prepare_bell_edges_tr cconf nkey
    (fun a b => (Kc * ngm_delta tm m a b + 1)%Z) es.

Lemma ng_weighted_bell_pass_tr_spec : forall tm m Kc es st,
  weighted_bell_pass_tr (ng_bell_edges_tr tm m Kc es) st =
  bell_pass tm m Kc es st.
Proof.
  intros. unfold ng_bell_edges_tr.
  rewrite weighted_bell_pass_tr_spec.
  symmetry. apply bell_pass_self_spec.
Qed.

Lemma ng_weighted_bell_iter_tr_spec : forall fuel tm m Kc es dist,
  weighted_bell_iter_tr fuel (ng_bell_edges_tr tm m Kc es) dist =
  bell_iter fuel tm m Kc es dist.
Proof.
  induction fuel as [|fuel IH]; intros tm m Kc es dist.
  - reflexivity.
  - change
      ((let '(dist', changed) := weighted_bell_pass_tr
           (ng_bell_edges_tr tm m Kc es) (dist, false) in
        if changed then weighted_bell_iter_tr fuel
           (ng_bell_edges_tr tm m Kc es) dist' else Some dist') =
       (let '(dist', changed) := bell_pass tm m Kc es (dist, false) in
        if changed then bell_iter fuel tm m Kc es dist' else Some dist')).
    rewrite ng_weighted_bell_pass_tr_spec.
    destruct (bell_pass tm m Kc es (dist, false)) as [dist' changed].
    destruct changed; [apply IH | reflexivity].
Qed.

Definition try_rule_b_weighted_tr (tm : TM) (g : Adj)
    (cset : PositiveSet.t) (c : list cconf) (Kc : nat) (m : ngmeas)
    : option (ngcomp * Adj) :=
  let es := intra_edges g cset c in
  let KcZ := Z.of_nat Kc in
  if ng_bad_self tm m KcZ es then None else
  (* This allocation is deliberately after the unchanged early rejection. *)
  let wes := ng_bell_edges_tr tm m KcZ es in
  match weighted_bell_iter_tr (S (length c)) wes (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (bell_get dist v - mn)%Z)) c in
      Some (NgMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Lemma try_rule_b_weighted_tr_spec : forall tm g cset c Kc m,
  try_rule_b_weighted_tr tm g cset c Kc m = try_rule_b tm g cset c Kc m.
Proof.
  intros. unfold try_rule_b_weighted_tr, try_rule_b.
  destruct (ng_bad_self tm m (Z.of_nat Kc) (intra_edges g cset c));
    [reflexivity |].
  now rewrite ng_weighted_bell_iter_tr_spec.
Qed.

Lemma first_some_rule_b_weighted_tr_spec : forall tm g cset c Kc ms,
  first_some (try_rule_b_weighted_tr tm g cset c Kc) ms =
  first_some (try_rule_b tm g cset c Kc) ms.
Proof.
  intros tm g cset c Kc ms. induction ms as [|m ms IH].
  - reflexivity.
  - cbn [first_some]. rewrite try_rule_b_weighted_tr_spec.
    destruct (try_rule_b tm g cset c Kc m); [reflexivity | exact IH].
Qed.

Definition process_scc_weighted_tr (tm : TM) (Kc : nat)
    (st : Adj * list ngcomp * bool) (c : list cconf)
    : Adj * list ngcomp * bool :=
  let '(g, acc, prog) := st in
  let cset := cset_of c in
  match first_some (try_rule_a tm g cset c) measures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match first_some (try_rule_b_weighted_tr tm g cset c Kc) measures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

Lemma process_scc_weighted_tr_spec : forall tm Kc st c,
  process_scc_weighted_tr tm Kc st c = process_scc tm Kc st c.
Proof.
  intros tm Kc [[g acc] prog] c.
  unfold process_scc_weighted_tr, process_scc.
  now rewrite first_some_rule_b_weighted_tr_spec.
Qed.

Lemma fold_process_scc_weighted_tr_spec : forall tm Kc cs st,
  fold_left (process_scc_weighted_tr tm Kc) cs st =
  fold_left (process_scc tm Kc) cs st.
Proof.
  intros tm Kc cs. induction cs as [|c cs IH]; intro st.
  - reflexivity.
  - cbn [fold_left]. rewrite process_scc_weighted_tr_spec. apply IH.
Qed.

Fixpoint proc_rounds_weighted_tr (fuel : nat) (tm : TM) (Kc rfuel : nat)
    (nodes : list cconf) (g : Adj) (acc : list ngcomp)
    : option (list ngcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := scc_partition rfuel nodes g in
      let cyc := filter (scc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (NgRank (node_rank nodes g) :: acc))
      | _ =>
          let acc' := NgRank (condensation_rank nodes g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (process_scc_weighted_tr tm Kc) cyc (g, acc', false) in
          if prog then proc_rounds_weighted_tr f tm Kc rfuel nodes g' acc''
          else None
      end
  end.

Lemma proc_rounds_weighted_tr_spec : forall fuel tm Kc rfuel nodes g acc,
  proc_rounds_weighted_tr fuel tm Kc rfuel nodes g acc =
  proc_rounds fuel tm Kc rfuel nodes g acc.
Proof.
  induction fuel as [|fuel IH]; intros tm Kc rfuel nodes g acc.
  - reflexivity.
  - cbn [proc_rounds_weighted_tr proc_rounds].
    destruct (filter (scc_cyclic g) (scc_partition rfuel nodes g))
      as [|c cs]; [reflexivity |].
    rewrite fold_process_scc_weighted_tr_spec.
    destruct (fold_left (process_scc tm Kc) (c :: cs)
      (g, NgRank (condensation_rank nodes g (scc_partition rfuel nodes g)) :: acc,
       false)) as [[g' acc'] prog].
    destruct prog; [apply IH | reflexivity].
Qed.
