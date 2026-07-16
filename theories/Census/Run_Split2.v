(** * Census/Run_Split2: splitting the largest grandchild once more.

    The A0=1RB, B0=1LC grandchild owns the census's largest single
    subtree computation; its machine reaches the undefined C1 slot at
    index 2, so the same expansion argument as
    [Run_Split.child_from_grandchildren] splits its Qed into the 16
    C1-fills (the pointer is StD, so every target is admissible),
    each certified by its own queue walk.  This file is strictly
    downstream of [Run_Split]: adding it invalidates none of the
    already-compiled per-grandchild computations. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run Run_Split.
Import ListNotations.

Set Default Goal Selector "!".

(** the machine of [gchild S1 S1 DL StC]: A0=1RB, B0=1LC *)
Definition tm_gg : TM :=
  TM_upd' (tm_child S1) StB S0 (Some (mkTrans S1 DL StC)).

Definition ggchild (w3 : Sym) (d3 : Dir) (nx3 : St) : TNF_Node :=
  mkNode (TM_upd' tm_gg StC S1 (Some (mkTrans w3 d3 nx3)))
         (ptr_after (Some StD) nx3).

Definition q_ggsub (w3 : Sym) (d3 : Dir) (nx3 : St) : SearchQueue :=
  ([ggchild w3 d3 nx3], []).

Lemma tm_gg_C_used : ~ UnusedState tm_gg StC.
Proof.
  intros (Hin & _ & _).
  refine (Hin StB S0 (mkTrans S1 DL StC) _ eq_refl).
  reflexivity.
Qed.

Lemma ggchild_WF : forall w3 d3 nx3,
  trans_ok (Some StD) (mkTrans w3 d3 nx3) = true ->
  Node_WF (ggchild w3 d3 nx3).
Proof.
  intros w3 d3 nx3 Hok.
  unfold Node_WF, ggchild; simpl.
  rewrite TM_upd'_spec.
  apply (UnusedState_ptr_upd tm_gg StC S1 (mkTrans w3 d3 nx3) (Some StD)).
  - reflexivity.
  - exact tm_gg_C_used.
  - exact (gchild_WF S1 S1 DL StC eq_refl).
  - exact Hok.
Qed.

Lemma ggsub_decided : forall w3 d3 nx3 n,
  trans_ok (Some StD) (mkTrans w3 d3 nx3) = true ->
  Nat.iter n q_suc (q_ggsub w3 d3 nx3) = ([], []) ->
  NodeDecided B_census D_census (node_tm (ggchild w3 d3 nx3)).
Proof.
  intros w3 d3 nx3 n Hok Hempty.
  assert (HWF : SearchQueue_WF B_census D_census
                  (Nat.iter n q_suc (q_ggsub w3 d3 nx3))
                  (ggchild w3 d3 nx3)).
  { clear Hempty. induction n.
    - apply SearchQueue_init_spec. apply ggchild_WF. exact Hok.
    - simpl. apply SearchQueue_upds_spec; [exact IHn | exact decider_WF]. }
  rewrite Hempty in HWF.
  exact (SearchQueue_empty_decided B_census D_census _ HWF).
Qed.

(** the 16 great-grandchild facts cover the 1RB/1LC grandchild *)
Lemma gchild_from_ggchildren :
  (forall w3 d3 nx3,
     trans_ok (Some StD) (mkTrans w3 d3 nx3) = true ->
     NodeDecided B_census D_census (node_tm (ggchild w3 d3 nx3))) ->
  NodeDecided B_census D_census (node_tm (gchild S1 S1 DL StC)).
Proof.
  intros Hg.
  assert (Hstep : stepn tm_gg 2 InitES =
                  Some (StC, tape_move DL S1 (tape_move DR S1
                               (mkTape blank_side S0 blank_side)))).
  { reflexivity. }
  assert (Hhole : tm_gg StC
                    (t_head (tape_move DL S1 (tape_move DR S1
                               (mkTape blank_side S0 blank_side))))
                  = None)
    by reflexivity.
  assert (HB : 3 <= B_census) by (unfold B_census; lia).
  pose proof (node_expand_spec B_census D_census tm_gg (Some StD) 2
                StC (tape_move DL S1 (tape_move DR S1
                       (mkTape blank_side S0 blank_side)))
                Hstep Hhole HB (gchild_WF S1 S1 DL StC eq_refl)) as [_ Hexp].
  change (NodeDecided B_census D_census tm_gg).
  apply Hexp.
  intros x' Hin.
  cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
       t_next t_head tape_move St_to_nat Nat.leb In] in Hin.
  destruct Hin
    as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
    cbn [node_tm];
    first
      [ exact (Hg S0 DL StA eq_refl) | exact (Hg S0 DL StB eq_refl)
      | exact (Hg S0 DL StC eq_refl) | exact (Hg S0 DL StD eq_refl)
      | exact (Hg S0 DR StA eq_refl) | exact (Hg S0 DR StB eq_refl)
      | exact (Hg S0 DR StC eq_refl) | exact (Hg S0 DR StD eq_refl)
      | exact (Hg S1 DL StA eq_refl) | exact (Hg S1 DL StB eq_refl)
      | exact (Hg S1 DL StC eq_refl) | exact (Hg S1 DL StD eq_refl)
      | exact (Hg S1 DR StA eq_refl) | exact (Hg S1 DR StB eq_refl)
      | exact (Hg S1 DR StC eq_refl) | exact (Hg S1 DR StD eq_refl) ].
Qed.
