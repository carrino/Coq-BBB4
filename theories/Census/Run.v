(** * Census/Run: the (4,2) quasihalting census, the Coq-BB5 way.

    Everything comes together: the TNF tree rooted at the all-undefined
    machine is walked by ONE in-Coq computation ([SearchQueue] +
    [Nat.iter]), every popped machine is decided by the verified
    pipeline ([Census/Decide.v]), and the queue emptying yields the
    census theorem

      [census_decided : forall tm, QHBound B_census tm \/
                                    Deferred D_census tm]

    -- every 4-state 2-symbol machine either has all its eventually-
    quiet states' last visits (BBB scores) bounded by [B_census], or
    lies in the swap/mirror/completion orbit of the explicit deferred
    list (the 3,713 BBB(4) holdouts plus the measured hard residue of
    the generic tiers).  No machine is ever named or stored: the tree
    IS the proof, exactly like Coq-BB5's BB(4) enumeration
    (Coq-BB5/CoqBB5/BB4/BB4_TNF_Enumeration.v).

    The root symmetrization mirrors BB5's: the four first-move-left
    children of the root are covered by their first-move-right mirror
    images ([node_decided_mirror]). *)

From Coq Require Import Arith Lia Bool List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs Deferred_Data.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Parameters *)

Definition B_census : nat := 2000.

Definition ng_rungs_census : list (nat * nat) :=
  [(2, 100); (3, 200); (4, 400); (6, 800)].

(** the rank-rules tier's ladder (mirrored by
    tools/sweep_rank_residue.py, which generates the deferred list) *)
Definition rank_rungs_census : list (nat * nat) :=
  [(3, 0); (3, 64); (3, 256); (3, 1024)].

(** the wrapped-QHBound tiers' ladder (mirrored by
    tools/sweep_qhbound_residue.py and tools/sweep_qhbound_lex.py;
    the measured catches all live at n <= 4, t <= 1024) *)
Definition qhb_rungs_census : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024)].

(** the RepWL tier's (L, T, t) ladder (mirrored by
    tools/sweep_repwl_residue.py): t = 0 only -- the 16-rung grid
    measured zero catches at t > 0 -- in measured yield order, so
    late-rung machines pay as few diverging-closure fuel burns as
    possible.  The fuel is the walk's per-rung cost bound; it covers
    every kept catch's closure (pops <= 2 * nodes + 1). *)
Definition rw_rungs_census : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].

Definition rw_fuel_census : nat := 8192.

Definition decider : QHDecider :=
  decide_easy B_census 130 512 200000 512 ng_rungs_census
              rank_rungs_census qhb_rungs_census rw_rungs_census
              rw_fuel_census (dmap_of D_census).

Lemma decider_WF : QHDecider_WF B_census D_census decider.
Proof.
  exact (decide_easy_WF B_census D_census 130 512 200000 512
           ng_rungs_census rank_rungs_census qhb_rungs_census
           rw_rungs_census rw_fuel_census).
Qed.

(** ** The root and its symmetrized first level *)

Definition TM0 : TM := fun _ _ => None.

Definition root : TNF_Node := mkNode TM0 (Some StB).

Lemma root_WF : Node_WF root.
Proof.
  unfold Node_WF, root; simpl.
  intro u.
  split.
  - intros (_ & _ & HA). destruct u; simpl; congruence || lia.
  - intro Hu. repeat split.
    + intros q s tr H. discriminate.
    + intro Hc. subst u. simpl in Hu. lia.
Qed.

(** the four first-move-right children of the root *)
Definition child (w : Sym) (d : Dir) (nx : St) : TNF_Node :=
  mkNode (TM_upd' TM0 StA S0 (Some (mkTrans w d nx)))
         (ptr_after (Some StB) nx).

Definition q_0 : SearchQueue :=
  ([child S0 DR StA; child S1 DR StA; child S0 DR StB; child S1 DR StB],
   []).

(** mirroring a one-transition machine flips its move direction *)
Lemma mirror_child : forall w d nx,
  mirror_tm (TM_upd' TM0 StA S0 (Some (mkTrans w d nx))) =
  TM_upd' TM0 StA S0 (Some (mkTrans w (mirror_dir d) nx)).
Proof.
  intros w d nx.
  rewrite !TM_upd'_spec.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  unfold mirror_tm, TM_upd, TM0.
  destruct (st_eqb q StA && sym_eqb s S0); reflexivity.
Qed.

Lemma child_WF : forall w d nx,
  trans_ok (Some StB) (mkTrans w d nx) = true ->
  Node_WF (child w d nx).
Proof.
  intros w d nx Hok.
  unfold Node_WF, child; simpl.
  rewrite TM_upd'_spec.
  apply (UnusedState_ptr_upd TM0 StA S0 (mkTrans w d nx) (Some StB)).
  - reflexivity.
  - intros (_ & _ & HA). congruence.
  - exact root_WF.
  - exact Hok.
Qed.

Lemma q_0_WF : SearchQueue_WF B_census D_census q_0 root.
Proof.
  assert (Hhole : TM0 StA S0 = None) by reflexivity.
  assert (Hstep : stepn TM0 0 InitES = Some (StA, mkTape blank_side S0 blank_side))
    by reflexivity.
  assert (HB : 1 <= B_census) by (unfold B_census; lia).
  pose proof (node_expand_spec B_census D_census TM0 (Some StB) 0 StA
                (mkTape blank_side S0 blank_side) Hstep Hhole HB
                (root_WF)) as [_ Hexp_dec].
  split.
  - (* the four children are well-formed *)
    intros x Hin.
    simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; apply child_WF; reflexivity.
  - (* the four children cover the root *)
    intros Hd.
    change (NodeDecided B_census D_census TM0).
    apply Hexp_dec.
    intros x' Hin.
    cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
         t_next t_head St_to_nat Nat.leb In] in Hin.
    (* the 8 in-range fills, in all_trans order: 4 left-movers (covered
       by their mirrors) and 4 right-movers (in the queue) *)
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      cbn [node_tm].
    + (* S0 DL StA: mirror of child S0 DR StA *)
      apply node_decided_mirror.
      rewrite (mirror_child S0 DL StA). cbn [mirror_dir].
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DL StB *)
      apply node_decided_mirror.
      rewrite (mirror_child S0 DL StB). cbn [mirror_dir].
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S0 DR StA *)
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DR StB *)
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S1 DL StA *)
      apply node_decided_mirror.
      rewrite (mirror_child S1 DL StA). cbn [mirror_dir].
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DL StB *)
      apply node_decided_mirror.
      rewrite (mirror_child S1 DL StB). cbn [mirror_dir].
      apply (Hd (child S1 DR StB)). simpl; tauto.
    + (* S1 DR StA *)
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DR StB *)
      apply (Hd (child S1 DR StB)). simpl; tauto.
Qed.

(** ** The walk *)

Definition q_suc (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider 13.

Lemma q_iter_WF : forall n,
  SearchQueue_WF B_census D_census (Nat.iter n q_suc q_0) root.
Proof.
  induction n.
  - exact q_0_WF.
  - simpl.
    apply SearchQueue_upds_spec; [exact IHn | exact decider_WF].
Qed.

(** ** The theorem, conditional on the computation emptying the queue *)

Lemma census_from_empty :
  forall n, Nat.iter n q_suc q_0 = ([], []) ->
  forall tm, QHBound B_census tm \/ Deferred D_census tm.
Proof.
  intros n Hempty tm.
  pose proof (q_iter_WF n) as HWF.
  rewrite Hempty in HWF.
  pose proof (SearchQueue_empty_decided B_census D_census root HWF) as Hnd.
  exact (Hnd tm (TM_le_TM0 (node_tm root) tm (fun _ _ => eq_refl))).
Qed.
