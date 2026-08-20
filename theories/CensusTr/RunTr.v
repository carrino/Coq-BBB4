(** * CensusTr/RunTr: the transition-level census walk wiring.

    The transition-level analogue of Census/Run.v + Run_Compute.v, in
    COLLECTION MODE: the three lookup tiers (proven / proven-QH /
    deferred) start EMPTY, so the walk decides the halt + cycle bulk
    and pushes everything else to the back queue.  The back queue of a
    completed collection walk IS the transition-level deferred set --
    it gets frozen into generated DeferredTr tables, this file's lists
    are regenerated, and the re-walk with the frozen list yields the
    census theorem, exactly the bootstrap the state census used.

    The walk computation ([SearchQueue], [Nat.iter], the [node_expand]
    tree) is the state census's own, reused by import; the decider is
    CensusTr/DecideTr.v's phase-0 stack.  Iterating [q_suc_tr] past
    queue exhaustion is a no-op ([SearchQueue_upds] returns the queue
    unchanged once the front list is empty), so a generous iteration
    count is safe for driver units.

    [census_tr_from_empty] states the conditional theorem now, with
    the empty deferred list: it becomes the real census theorem the
    moment a walk over the FROZEN regenerated list empties the queue. *)

From Coq Require Import Arith Lia Bool List NArith.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import TNF_QHTr DecideTr.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Parameters: collection mode *)

Definition B_tr : nat := 2000.

Definition D_tr : list TM := [].
Definition prov_tr : list TM := [].
Definition provqh_tr : list TM := [].

Lemma prov_tr_all : Forall NeverQuasiHaltsTr prov_tr.
Proof. constructor. Qed.

Lemma provqh_tr_all :
  Forall (fun tm => NonHalt tm /\ QHBoundTr B_tr tm /\ QuasiHaltsTr tm)
         provqh_tr.
Proof. constructor. Qed.

(** the same rung ladders as the state census (Run_Compute.v), and the
    same n-gram fuel/rounds *)
Definition ng_rungs_tr : list (nat * nat) :=
  [(2, 100); (3, 200); (4, 400); (6, 800)].

(** the rank-rules never tier's ladder, the state census's own
    (Run_Compute.v [rank_rungs_census]) *)
Definition rank_rungs_tr : list (nat * nat) :=
  [(3, 0); (3, 64); (3, 256); (3, 1024)].

Definition qhb_rungs_tr : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024)].

(** the lex ladder is the expensive one (per rung: re-grow, explore,
    certificate search per instruction), and a failing machine pays
    every rung -- so it gets the single deepest horizon per window,
    and no n >= 5 rungs in-walk (context mixing at n <= 4 costs ~3/36
    pilot catches; those go to offline boards, PLAYBOOK Rule 4) *)
Definition qhb_lex_rungs_tr : list (nat * nat) :=
  [(2, 1024); (3, 1024); (4, 1024)].

(** the RepWL tier's parameters, the state census's own
    (Run_Compute.v [rw_rungs_census] / [rw_fuel_census] /
    [rw_cut_census]) *)
Definition rw_rungs_tr : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].
Definition rw_fuel_tr : nat := 5120.
Definition rw_cut_tr : nat := 32.

Definition decider_tr : QHDecider :=
  decide_easy_tr B_tr 130 512 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_rungs_tr rw_fuel_tr rw_cut_tr
    (dmap_of prov_tr) (dmap_of provqh_tr) (dmap_of D_tr).

Lemma decider_tr_WF : QHDeciderTr_WF B_tr D_tr decider_tr.
Proof.
  exact (decide_easy_tr_WF B_tr D_tr 130 512 200000 512
           ng_rungs_tr rank_rungs_tr qhb_rungs_tr qhb_lex_rungs_tr
           rw_rungs_tr rw_fuel_tr rw_cut_tr
           prov_tr prov_tr_all provqh_tr provqh_tr_all).
Qed.

(** ** The root and its symmetrized first level (Run_Compute.v shapes) *)

Definition TM0 : TM := fun _ _ => None.

Definition root : TNF_Node := mkNode TM0 (Some StB).

Definition child (w : Sym) (d : Dir) (nx : St) : TNF_Node :=
  mkNode (TM_upd' TM0 StA S0 (Some (mkTrans w d nx)))
         (ptr_after (Some StB) nx).

Definition q_0_tr : SearchQueue :=
  ([child S0 DR StA; child S1 DR StA; child S0 DR StB; child S1 DR StB],
   []).

Definition q_suc_tr (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_tr 13.

(** per-subtree roots, for splitting a long walk across processes *)
Definition q_sub_tr (w : Sym) (nx : St) : SearchQueue :=
  ([child w DR nx], []).

(** ** Well-formedness of the symmetrized root *)

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

Lemma q_0_tr_WF : SearchQueue_WF_Tr B_tr D_tr q_0_tr root.
Proof.
  assert (Hhole : TM0 StA S0 = None) by reflexivity.
  assert (Hstep : stepn TM0 0 InitES = Some (StA, mkTape blank_side S0 blank_side))
    by reflexivity.
  assert (HB : 1 <= B_tr) by (unfold B_tr; lia).
  pose proof (node_expand_tr_spec B_tr D_tr TM0 (Some StB) 0 StA
                (mkTape blank_side S0 blank_side) Hstep Hhole HB
                (root_WF)) as [_ Hexp_dec].
  split.
  - intros x Hin.
    simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; apply child_WF; reflexivity.
  - intros Hd.
    change (NodeDecidedTr B_tr D_tr TM0).
    apply Hexp_dec.
    intros x' Hin.
    cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
         t_next t_head St_to_nat Nat.leb In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      cbn [node_tm].
    + (* S0 DL StA: mirror of child S0 DR StA *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S0 DL StA). cbn [mirror_dir].
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DL StB *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S0 DL StB). cbn [mirror_dir].
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S0 DR StA *)
      apply (Hd (child S0 DR StA)). simpl; tauto.
    + (* S0 DR StB *)
      apply (Hd (child S0 DR StB)). simpl; tauto.
    + (* S1 DL StA *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S1 DL StA). cbn [mirror_dir].
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DL StB *)
      apply node_decided_tr_mirror.
      rewrite (mirror_child S1 DL StB). cbn [mirror_dir].
      apply (Hd (child S1 DR StB)). simpl; tauto.
    + (* S1 DR StA *)
      apply (Hd (child S1 DR StA)). simpl; tauto.
    + (* S1 DR StB *)
      apply (Hd (child S1 DR StB)). simpl; tauto.
Qed.

Lemma q_iter_tr_WF : forall n,
  SearchQueue_WF_Tr B_tr D_tr (Nat.iter n q_suc_tr q_0_tr) root.
Proof.
  induction n.
  - exact q_0_tr_WF.
  - simpl.
    apply SearchQueue_upds_spec_tr; [exact IHn | exact decider_tr_WF].
Qed.

(** ** The theorem, conditional on the computation emptying the queue *)

Lemma census_tr_from_empty :
  forall n, Nat.iter n q_suc_tr q_0_tr = ([], []) ->
  forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm.
Proof.
  intros n Hempty tm.
  pose proof (q_iter_tr_WF n) as HWF.
  rewrite Hempty in HWF.
  pose proof (SearchQueue_empty_decided_tr B_tr D_tr root HWF) as Hnd.
  exact (Hnd tm (TM_le_TM0 (node_tm root) tm (fun _ _ => eq_refl))).
Qed.

(** ** Collection-walk output helpers (untrusted serialization)

    [queue_encs] renders the back queue -- the deferred candidates --
    as [tm_enc] codes, printed by Coq as decimal [N] literals; the
    untrusted tools/censustr/decode_enc.py turns them back into
    bbchallenge machine text and DeferredTr tables. *)

Definition tm_row (tm : TM) : list (option Trans) :=
  [tm StA S0; tm StA S1; tm StB S0; tm StB S1;
   tm StC S0; tm StC S1; tm StD S0; tm StD S1].

Definition queue_sizes (q : SearchQueue) : nat * nat :=
  (length (fst q), length (snd q)).

Definition queue_encs (q : SearchQueue) : list N :=
  map (fun x => N.pos (tm_enc (node_tm x))) (snd q).

(** front-queue serialization for the FRONTIER SPLIT (parallel
    collection): each pending node as (machine code, TNF pointer
    code), so tools/censustr/gen_walk_shards.py can partition the
    frontier across independent shard processes.  Untrusted, like all
    collection serialization: the re-walk re-derives everything. *)
Definition ptr_enc (p : option St) : N :=
  match p with
  | None => 0
  | Some StA => 1
  | Some StB => 2
  | Some StC => 3
  | Some StD => 4
  end%N.

Definition queue_front_encs (q : SearchQueue) : list (N * N) :=
  map (fun x => (N.pos (tm_enc (node_tm x)), ptr_enc (node_ptr x)))
      (fst q).
