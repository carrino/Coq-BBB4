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
  Proven_Data ProvenQH_Data.
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
    tools/sweep_qhbound_residue.py and tools/sweep_qhbound_lex.py, and,
    for the larger-prefix extension, by measure_B/run_sweep.py).

    The first nine rungs (n <= 4, t <= 1024) were the original vocabulary.
    Lever B extends the prefix depth: an all-survivor sweep of the 9,775
    wrap-QH machines found 2,533 more caught by the SAME rank + count-lex
    gates at larger prefixes -- t in {1280, 1536, 1999} for n in {2, 3, 4}
    (per-rung yield 1545/156/4, 188/13/3, 607/16 -- (4,1999) caught none),
    plus a single machine at (6, 1999).  Every added rung keeps
    S t <= B_census = 2000, so t = 1999 is the deepest legal prefix; the
    n=5,6 and t=4096 probes the sweep also ran caught nothing usable under
    that bound and are omitted.  Rungs are a Section variable of the
    pipeline, so extending the list needs no soundness re-proof: try_qhb's
    per-rung [S t <=? B] gate rejects any illegal prefix. *)
(** PROVEN-ONLY (D_census 16,115): reverted to the original 19,735 rungs.
    Lever B's extended prefix rungs (t=1280/1536/1999) were tried on every
    machine reaching the qhb tier IN-WALK and made the census walk far
    heavier (GG_1LC units ~9min -> >1h) -- unsustainable under container
    preemption.  The lever-B machines stay DEFERRED (in the 16,115 list),
    caught by deferred_lookup before the rungs, so the walk is the light
    19,735 walk.  (Re-add the extended rungs only with a stable long-lived
    compute env; see NEXT_SESSION post-mortem.) *)
Definition qhb_rungs_census : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024)].

(** the RepWL tier's (L, T, t) ladder (mirrored by
    tools/sweep_repwl_residue.py for the first four rungs and by
    tools/sweep_repwl2.py for the block-width extension): t = 0 only --
    the 16-rung grid measured zero catches at t > 0 -- in measured
    yield order, so late-rung machines pay as few diverging-closure
    fuel burns as possible.  The fuel is the walk's per-rung cost
    bound; it covers every kept catch's closure (pops <= 2 * nodes + 1).

    Lever C extends the block width: an all-survivor sweep of the 6,247
    never-QH residue machines (tools/repwl2_caught.tsv) found 592 more
    caught by the SAME rules (a)/(b) over the five built-in measures at
    wider blocks -- rungs (5, 2, 0), (6, 2, 0), (7, 2, 0), per-rung
    yield 223 / 273 / 96, disjoint.  (6, 2, 0) is placed LAST because it
    is the only expensive-diverging new rung; a machine caught at
    (5, 2, 0) or (7, 2, 0) never pays the diverging (6, 2, 0) closure.
    Measured zero marginal yield at T >= 3 / T = 4 and at 2x/4x fuel, so
    neither the threshold nor the fuel is raised; no new measure kind is
    needed (the 5 built-ins discharge all 592: 400 plain-rank rule (a),
    192 measure-lex rule (b)).  Rungs are a Section variable, so
    extending the list needs no soundness re-proof.

    The fuel is TIGHT: the largest kept catch closes in 7947 nodes /
    8145 pops (fuel need 8146); rw_fuel_census = 8192 leaves 46 pops of
    headroom, so any catch needing more stays deferred rather than
    silently raising the bound. *)
(** PROVEN-ONLY: reverted to the original 19,735 four rungs (lever C's
    wider blocks (5/6/7,2,0) also load the walk; its machines stay
    deferred). *)
Definition rw_rungs_census : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].

Definition rw_fuel_census : nat := 8192.

(** the proven-machines map, built once from [proven_list] (mirrors how
    [dmap_of D_census] is applied inside [decider]); a hit is decided
    R_NeverQH by [proven_all]'s [Forall NeverQuasiHaltsSt] certificate. *)
Definition pmap : DeferredMap := dmap_of proven_list.

(** the proven-QH map, built once from [provenqh_list] (the R_QH sibling of
    [pmap]); a hit is decided R_QH by [provenqh_all]'s [Forall (NonHalt /\
    QHBound B_census /\ QuasiHaltsSt)] certificate. *)
Definition qhmap : DeferredMap := dmap_of provenqh_list.

Definition decider : QHDecider :=
  decide_easy B_census 130 512 200000 512 ng_rungs_census
              rank_rungs_census qhb_rungs_census rw_rungs_census
              rw_fuel_census pmap qhmap (dmap_of D_census).

Lemma decider_WF : QHDecider_WF B_census D_census decider.
Proof.
  exact (decide_easy_WF B_census D_census 130 512 200000 512
           ng_rungs_census rank_rungs_census qhb_rungs_census
           rw_rungs_census rw_fuel_census proven_list proven_all
           provenqh_list provenqh_all).
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
