(** Ordered precomputed edge weights for instruction-level certificate search.

    The immutable edge list is prepared once for a Bellman-Ford attempt.
    The pass retains the original left-to-right updates, missing-distance
    default, changed flag and fuel behavior. No checker or search guard is
    replaced by this helper. *)
From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4.Census Require Import BellmanFord.
Import ListNotations.

Definition weighted_edge_tr : Type := (positive * positive * Z)%type.

Definition prepare_bell_edges_tr (A : Type) (key : A -> positive)
    (weight : A -> A -> Z) (es : list (A * A)) : list weighted_edge_tr :=
  map (fun '(a, b) => (key a, key b, weight a b)) es.

Definition weighted_relax_tr (st : PositiveMap.tree Z * bool)
    (e : weighted_edge_tr) : PositiveMap.tree Z * bool :=
  let '(dist, changed) := st in
  let '(a, b, weight) := e in
  let da := match PositiveMap.find a dist with Some v => v | None => 0%Z end in
  let db := match PositiveMap.find b dist with Some v => v | None => 0%Z end in
  let candidate := (da - weight)%Z in
  if Z.ltb candidate db
  then (PositiveMap.add b candidate dist, true)
  else (dist, changed).

Definition weighted_bell_pass_tr (es : list weighted_edge_tr)
    (st : PositiveMap.tree Z * bool) : PositiveMap.tree Z * bool :=
  fold_left weighted_relax_tr es st.

Fixpoint weighted_bell_iter_tr (fuel : nat) (es : list weighted_edge_tr)
    (dist : PositiveMap.tree Z) : option (PositiveMap.tree Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(dist', changed) := weighted_bell_pass_tr es (dist, false) in
      if changed then weighted_bell_iter_tr fuel' es dist' else Some dist'
  end.

Lemma weighted_bell_pass_tr_spec : forall A key weight es st,
  weighted_bell_pass_tr (prepare_bell_edges_tr A key weight es) st =
  fold_left (self_relax A key weight) es st.
Proof.
  intros A key weight es. unfold weighted_bell_pass_tr, prepare_bell_edges_tr.
  induction es as [|[a b] es IH]; intros st; [reflexivity|].
  cbn [map fold_left]. rewrite IH.
  destruct st as [dist changed]. reflexivity.
Qed.

(** Reference recurrence over the existing generic relaxation, used only to
    state a generic exact equality. Production callers use weighted_bell_iter_tr. *)
Fixpoint self_bell_iter_tr (A : Type) (key : A -> positive)
    (weight : A -> A -> Z) (fuel : nat) (es : list (A * A))
    (dist : PositiveMap.tree Z) : option (PositiveMap.tree Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(dist', changed) := fold_left (self_relax A key weight) es (dist, false) in
      if changed then self_bell_iter_tr A key weight fuel' es dist' else Some dist'
  end.

Lemma weighted_bell_iter_tr_spec : forall A key weight fuel es dist,
  weighted_bell_iter_tr fuel (prepare_bell_edges_tr A key weight es) dist =
  self_bell_iter_tr A key weight fuel es dist.
Proof.
  intros A key weight fuel. induction fuel as [|fuel IH]; intros es dist;
    [reflexivity|].
  change
    ((let '(dist', changed) := weighted_bell_pass_tr
          (prepare_bell_edges_tr A key weight es) (dist, false) in
      if changed then weighted_bell_iter_tr fuel
          (prepare_bell_edges_tr A key weight es) dist' else Some dist') =
     (let '(dist', changed) := fold_left (self_relax A key weight) es (dist, false) in
      if changed then self_bell_iter_tr A key weight fuel es dist' else Some dist')).
  rewrite weighted_bell_pass_tr_spec.
  destruct (fold_left (self_relax A key weight) es (dist, false))
    as [dist' changed].
  destruct changed; [apply IH|reflexivity].
Qed.
