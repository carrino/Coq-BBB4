(** * Census/Run_Split: the census walk, one subtree per computation.

    The tree under each of the four root children is walked by its own
    [Nat.iter] (so the four heavy computations can live in separate
    files and compile in parallel, BB5's TNF_Enumeration_Roots trick);
    the root is then covered by the four [NodeDecided] facts through
    the same expansion + mirror argument as [Run.q_0_WF]. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run.
Import ListNotations.

Set Default Goal Selector "!".

Definition q_sub (w : Sym) (nx : St) : SearchQueue :=
  ([child w DR nx], []).

Lemma q_sub_WF : forall w nx,
  trans_ok (Some StB) (mkTrans w DR nx) = true ->
  SearchQueue_WF B_census D_census (q_sub w nx) (child w DR nx).
Proof.
  intros w nx Hok.
  apply SearchQueue_init_spec.
  apply child_WF.
  exact Hok.
Qed.

Lemma sub_decided : forall w nx n,
  trans_ok (Some StB) (mkTrans w DR nx) = true ->
  Nat.iter n q_suc (q_sub w nx) = ([], []) ->
  NodeDecided B_census D_census (node_tm (child w DR nx)).
Proof.
  intros w nx n Hok Hempty.
  assert (HWF : SearchQueue_WF B_census D_census
                  (Nat.iter n q_suc (q_sub w nx)) (child w DR nx)).
  { clear Hempty. induction n.
    - apply q_sub_WF; exact Hok.
    - simpl. apply SearchQueue_upds_spec; [exact IHn | exact decider_WF]. }
  rewrite Hempty in HWF.
  exact (SearchQueue_empty_decided B_census D_census _ HWF).
Qed.

(** the four subtree facts cover every machine *)
Lemma census_from_subtrees :
  NodeDecided B_census D_census (node_tm (child S0 DR StA)) ->
  NodeDecided B_census D_census (node_tm (child S1 DR StA)) ->
  NodeDecided B_census D_census (node_tm (child S0 DR StB)) ->
  NodeDecided B_census D_census (node_tm (child S1 DR StB)) ->
  forall tm, QHBound B_census tm \/ Deferred D_census tm.
Proof.
  intros H0A H1A H0B H1B tm.
  destruct q_0_WF as [_ Hcover].
  refine (Hcover _ tm (TM_le_TM0 (node_tm root) tm (fun _ _ => eq_refl))).
  intros x Hin.
  simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; assumption.
Qed.
