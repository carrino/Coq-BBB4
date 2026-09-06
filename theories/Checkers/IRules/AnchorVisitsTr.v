(** * Checkers/IRules/AnchorVisitsTr: fused anchor walk + INSTRUCTION mask.

    The transition-level analogue of AnchorVisits.v: one anchor-prefix
    pass computing the final configuration together with the set of
    FIRED INSTRUCTIONS (state, read symbol) of configurations
    [0 .. n-1].  The instruction mask is a pair of per-state masks,
    one per read symbol, so the state machinery reuses [vmask].

    The completeness lemma [csteps_tvis_complete] is what the Tr meta
    checker's prefix gate stands on: an instruction fired anywhere in
    the walked prefix is in the mask. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Engine AnchorVisits.
Import ListNotations.

Set Default Goal Selector "!".

(** fired-instruction mask: a visited-state mask per read symbol *)
Definition tmask : Type := (vmask * vmask).

Definition tvm_empty : tmask := (vm_empty, vm_empty).

Definition tvm_get (v : tmask) (t : Tr) : bool :=
  let '(v0, v1) := v in
  match snd t with S0 => vm_get v0 (fst t) | S1 => vm_get v1 (fst t) end.

Definition tvm_add (v : tmask) (t : Tr) : tmask :=
  let '(v0, v1) := v in
  match snd t with
  | S0 => (vm_add v0 (fst t), v1)
  | S1 => (v0, vm_add v1 (fst t))
  end.

Lemma tvm_add_get : forall v t t',
  tvm_get (tvm_add v t) t' = (instr_eqb t' t || tvm_get v t').
Proof.
  intros [v0 v1] [q s] [q' s'].
  unfold instr_eqb; destruct s, s'; simpl;
    rewrite ?vm_add_get, ?andb_true_r, ?andb_false_r; reflexivity.
Qed.

(** the instruction a [cconf] is about to fire *)
Definition cinstr (c : cconf) : Tr :=
  (fst c, let '(_, h, _) := snd c in h).

Lemma cinstr_lift : forall c, instr_of (lift c) = cinstr c.
Proof. intros [q [[l h] r]]. reflexivity. Qed.

(** the fused walk: instructions of configurations [0 .. n-1] plus the
    configuration at [n] *)
Fixpoint csteps_tvis (tm : TM) (n : nat) (c : cconf) (v : tmask)
  : option (cconf * tmask) :=
  match n with
  | 0 => Some (c, v)
  | S m =>
      let v' := tvm_add v (cinstr c) in
      match cstep tm c with
      | None => None
      | Some c' => csteps_tvis tm m c' v'
      end
  end.

Lemma csteps_tvis_csteps : forall tm n c v c' tvis,
  csteps_tvis tm n c v = Some (c', tvis) ->
  csteps tm n c = Some c'.
Proof.
  intros tm n; induction n as [|m IH]; intros c v c' tvis H; simpl in *.
  - injection H as <- <-. reflexivity.
  - destruct (cstep tm c) as [c1|]; [|discriminate].
    exact (IH c1 _ c' tvis H).
Qed.

Lemma csteps_tvis_mono : forall tm n c v c' tvis t,
  csteps_tvis tm n c v = Some (c', tvis) ->
  tvm_get v t = true -> tvm_get tvis t = true.
Proof.
  intros tm n; induction n as [|m IH]; intros c v c' tvis t H Hv;
    simpl in H.
  - injection H as <- <-. exact Hv.
  - destruct (cstep tm c) as [c1|]; [|discriminate].
    apply (IH c1 (tvm_add v (cinstr c)) c' tvis t H).
    rewrite tvm_add_get, Hv. apply orb_true_r.
Qed.

(** completeness: any instruction fired at an index inside the walked
    prefix is in the final mask *)
Lemma csteps_tvis_complete : forall tm n c v c' tvis m cm,
  csteps_tvis tm n c v = Some (c', tvis) ->
  (m < n)%nat ->
  csteps tm m c = Some cm ->
  tvm_get tvis (cinstr cm) = true.
Proof.
  intros tm n; induction n as [|n IH]; intros c v c' tvis m cm H Hm Hc;
    [lia|].
  simpl in H.
  destruct (cstep tm c) as [c1|] eqn:Hs; [|discriminate].
  destruct m as [|m].
  - simpl in Hc. injection Hc as ->.
    apply (csteps_tvis_mono tm n c1 _ c' tvis _ H).
    rewrite tvm_add_get.
    rewrite (proj2 (instr_eqb_spec (cinstr cm) (cinstr cm)) eq_refl).
    reflexivity.
  - simpl in Hc. rewrite Hs in Hc.
    exact (IH c1 _ c' tvis m cm H ltac:(lia) Hc).
Qed.
