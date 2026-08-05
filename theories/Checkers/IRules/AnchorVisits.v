(** * Checkers/IRules/AnchorVisits: fused anchor walk + visit mask.

    The IRules meta checkers previously ran [csteps] over the anchor
    prefix (millions of steps) and then [cvisits] once per state --
    up to five full anchor-length simulations per machine.  One pass
    computes the final configuration and the set of visited states
    together; the bridge lemmas let the existing soundness proofs
    (which reason through [cvisits]) transport unchanged. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

Set Default Goal Selector "!".

(** visited-state mask: one bool per state *)
Definition vmask : Type := (bool * bool * bool * bool).

Definition vm_empty : vmask := (false, false, false, false).

Definition vm_get (v : vmask) (q : St) : bool :=
  let '(a, b, c, d) := v in
  match q with StA => a | StB => b | StC => c | StD => d end.

Definition vm_add (v : vmask) (q : St) : vmask :=
  let '(a, b, c, d) := v in
  match q with
  | StA => (true, b, c, d)
  | StB => (a, true, c, d)
  | StC => (a, b, true, d)
  | StD => (a, b, c, true)
  end.

Lemma vm_add_get : forall v q q',
  vm_get (vm_add v q) q' = (st_eqb q' q || vm_get v q').
Proof.
  intros [[[a b] c] d] q q'; destruct q, q'; reflexivity.
Qed.

(** the fused walk: states of configurations [0 .. n-1] (exactly
    [cvisits]'s range) plus the configuration at [n] *)
Fixpoint csteps_vis (tm : TM) (n : nat) (c : cconf) (v : vmask)
  : option (cconf * vmask) :=
  match n with
  | 0 => Some (c, v)
  | S m =>
      let v' := vm_add v (fst c) in
      match cstep tm c with
      | None => None
      | Some c' => csteps_vis tm m c' v'
      end
  end.

Lemma csteps_vis_csteps : forall tm n c v c' vis,
  csteps_vis tm n c v = Some (c', vis) ->
  csteps tm n c = Some c'.
Proof.
  intros tm n; induction n as [|m IH]; intros c v c' vis H; simpl in *.
  - injection H as <- <-. reflexivity.
  - destruct (cstep tm c) as [c1|]; [|discriminate].
    exact (IH c1 _ c' vis H).
Qed.

Lemma csteps_vis_mono : forall tm n c v c' vis q,
  csteps_vis tm n c v = Some (c', vis) ->
  vm_get v q = true -> vm_get vis q = true.
Proof.
  intros tm n; induction n as [|m IH]; intros c v c' vis q H Hv;
    simpl in H.
  - injection H as <- <-. exact Hv.
  - destruct (cstep tm c) as [c1|]; [|discriminate].
    apply (IH c1 (vm_add v (fst c)) c' vis q H).
    rewrite vm_add_get, Hv. apply orb_true_r.
Qed.

Lemma cvisits_csteps_vis : forall tm n c v c' vis q,
  csteps_vis tm n c v = Some (c', vis) ->
  cvisits tm c n q = true ->
  vm_get vis q = true.
Proof.
  intros tm n; induction n as [|m IH]; intros c v c' vis q H Hc;
    simpl in *; [discriminate|].
  destruct (cstep tm c) as [c1|] eqn:Hs; [|discriminate].
  apply orb_prop in Hc as [Hc | Hc].
  - apply (csteps_vis_mono tm m c1 _ c' vis q H).
    rewrite vm_add_get.
    apply st_eqb_spec in Hc. subst q.
    destruct (fst c); simpl; reflexivity.
  - exact (IH c1 _ c' vis q H Hc).
Qed.
