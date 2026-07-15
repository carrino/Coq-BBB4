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

(** ** One level deeper: the xRB children split into 12 grandchildren

    The wRB child (w in {S0, S1}) halts at index 1 in state B reading
    the blank; its expansion fills B0 with the 12 in-range
    transitions (targets up to the pointer StC).  Splitting there
    makes the two heavy walks 12 parallel walks each, bounding the
    certification wall-time by the largest grandchild subtree. *)

Definition tm_child (w : Sym) : TM :=
  TM_upd' TM0 StA S0 (Some (mkTrans w DR StB)).

Definition gchild (w w2 : Sym) (d2 : Dir) (nx2 : St) : TNF_Node :=
  mkNode (TM_upd' (tm_child w) StB S0 (Some (mkTrans w2 d2 nx2)))
         (ptr_after (Some StC) nx2).

Definition q_gsub (w w2 : Sym) (d2 : Dir) (nx2 : St) : SearchQueue :=
  ([gchild w w2 d2 nx2], []).

Lemma tm_child_B0_used : forall w, ~ UnusedState (tm_child w) StB.
Proof.
  intros w (Hin & _ & _).
  refine (Hin StA S0 (mkTrans w DR StB) _ eq_refl).
  destruct w; reflexivity.
Qed.

Lemma gchild_WF : forall w w2 d2 nx2,
  trans_ok (Some StC) (mkTrans w2 d2 nx2) = true ->
  Node_WF (gchild w w2 d2 nx2).
Proof.
  intros w w2 d2 nx2 Hok.
  unfold Node_WF, gchild; simpl.
  rewrite TM_upd'_spec.
  apply (UnusedState_ptr_upd (tm_child w) StB S0 (mkTrans w2 d2 nx2)
           (Some StC)).
  - destruct w; reflexivity.
  - apply tm_child_B0_used.
  - exact (child_WF w DR StB eq_refl).
  - exact Hok.
Qed.

Lemma gsub_decided : forall w w2 d2 nx2 n,
  trans_ok (Some StC) (mkTrans w2 d2 nx2) = true ->
  Nat.iter n q_suc (q_gsub w w2 d2 nx2) = ([], []) ->
  NodeDecided B_census D_census (node_tm (gchild w w2 d2 nx2)).
Proof.
  intros w w2 d2 nx2 n Hok Hempty.
  assert (HWF : SearchQueue_WF B_census D_census
                  (Nat.iter n q_suc (q_gsub w w2 d2 nx2))
                  (gchild w w2 d2 nx2)).
  { clear Hempty. induction n.
    - apply SearchQueue_init_spec. apply gchild_WF. exact Hok.
    - simpl. apply SearchQueue_upds_spec; [exact IHn | exact decider_WF]. }
  rewrite Hempty in HWF.
  exact (SearchQueue_empty_decided B_census D_census _ HWF).
Qed.

(** the 12 grandchild facts cover the wRB child *)
Lemma child_from_grandchildren : forall w,
  (forall w2 d2 nx2,
     trans_ok (Some StC) (mkTrans w2 d2 nx2) = true ->
     NodeDecided B_census D_census (node_tm (gchild w w2 d2 nx2))) ->
  NodeDecided B_census D_census (node_tm (child w DR StB)).
Proof.
  intros w Hg.
  assert (Hstep : stepn (tm_child w) 1 InitES =
                  Some (StB, tape_move DR w (mkTape blank_side S0 blank_side))).
  { destruct w; reflexivity. }
  assert (Hhole : tm_child w StB
                    (t_head (tape_move DR w (mkTape blank_side S0 blank_side)))
                  = None)
    by (destruct w; reflexivity).
  assert (HB : 2 <= B_census) by (unfold B_census; lia).
  pose proof (node_expand_spec B_census D_census (tm_child w) (Some StC) 1
                StB (tape_move DR w (mkTape blank_side S0 blank_side))
                Hstep Hhole HB (child_WF w DR StB eq_refl)) as [_ Hexp].
  change (NodeDecided B_census D_census (tm_child w)).
  apply Hexp.
  intros x' Hin.
  cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
       t_next t_head tape_move St_to_nat Nat.leb In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
    cbn [node_tm];
    first
      [ exact (Hg S0 DL StA eq_refl) | exact (Hg S0 DL StB eq_refl)
      | exact (Hg S0 DL StC eq_refl) | exact (Hg S0 DR StA eq_refl)
      | exact (Hg S0 DR StB eq_refl) | exact (Hg S0 DR StC eq_refl)
      | exact (Hg S1 DL StA eq_refl) | exact (Hg S1 DL StB eq_refl)
      | exact (Hg S1 DL StC eq_refl) | exact (Hg S1 DR StA eq_refl)
      | exact (Hg S1 DR StB eq_refl) | exact (Hg S1 DR StC eq_refl) ].
Qed.
