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
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs Deferred_Data
  Proven_Data ProvenQH_Data RerootQH_Data Proven_List ProvenQH_List.
(** EXPORT, not Import: [B_census], [decider], [q_0], [q_suc] and the
    rest moved to Run_Compute, and every existing client of Run.v --
    Run_Split, Run_Split2, the walk units, Closeout -- names them
    unqualified.  Exporting keeps all of them compiling untouched, so
    the split costs no edits outside this file. *)
From BBB4.Census Require Export Run_Compute.
Import ListNotations.

Set Default Goal Selector "!".

(** ** The certificates, re-attached to the DATA lists

    [Run_Compute] builds the lookup maps from the data-only lists so a
    walk unit never loads the boards (docs/CENSUS_RUNTIME.md: 5.32 GB
    and 25 s per unit, natively, before deciding anything).  These two
    lemmas are what keeps the split honest, and they are not proofs so
    much as type-checks: [proven_all] is a certificate about
    [proven_list], and it is accepted here as one about
    [proven_list_data] ONLY because the kernel finds the two lists
    convertible.  Regenerate one without the other -- drop a machine,
    duplicate one, reorder them -- and this file stops compiling.  No
    sampling, no diff, no way to get it wrong quietly. *)

Lemma proven_list_data_all : Forall NeverQuasiHaltsSt proven_list_data.
Proof. exact proven_all. Qed.

(** its in-Coq certificate: each machine is non-halting, has every quiet
    state's last visit bounded by [B_census] ([QHBound]), and quasihalts
    -- exactly the [R_QH] contract, so a lookup hit discharges it.
    [provenqh_all] is about [provenqh_list] and is accepted about
    [provenqh_list_data] by the same conversion; [reroot_qh_list] is the
    real list (its machines are [row_to_tm] applications, which are not
    convertible to literal transition tables, and it costs ~0.08 GB). *)
Lemma reroot_provenqh_all :
  Forall (fun tm => NonHalt tm /\ QHBound B_census tm /\ QuasiHaltsSt tm)
         (provenqh_list_data ++ reroot_qh_list).
Proof.
  apply Forall_app; split; [exact provenqh_all | exact reroot_qh_all].
Qed.

Lemma decider_WF : QHDecider_WF B_census D_census decider.
Proof.
  exact (decide_easy_WF B_census D_census 130 512 200000 512
           ng_rungs_census rank_rungs_census qhb_rungs_census
           rw_rungs_census rw_fuel_census proven_list_data
           proven_list_data_all
           (provenqh_list_data ++ reroot_qh_list) reroot_provenqh_all
           hmap_census).
Qed.

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
