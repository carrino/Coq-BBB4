(** Waiting-specific soundness for the existing TNF search machinery.
    Qualitative recurrence classifications alone discharge no waiting leaf. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport.
Import ListNotations.

Section WaitingCensus.
Variables B wait_width : nat.
Variable D : list TM.

Definition Decided (tm : TM) : Prop := WindowBound tm B wait_width \/ Deferred D tm.
Definition NodeDecided (tm : TM) : Prop := forall tm', TM_le tm tm' -> Decided tm'.

Lemma node_decided_leaf : forall tm,
 NonHalt tm -> WindowBound tm B wait_width -> NodeDecided tm.
Proof.
 intros tm Hnh HW tm' Hle; left.
 apply (proj2 (window_bound_completion tm tm' B wait_width Hnh Hle)); exact HW.
Qed.
Lemma node_decided_deferred : forall tm, In tm D -> NodeDecided tm.
Proof. intros tm H tm' Hle; right; exact (Deferred_base D tm tm' H Hle). Qed.
Lemma decided_unswap : forall u v tm,
 u <> v -> u <> StA -> v <> StA -> Decided (TM_swap u v tm) -> Decided tm.
Proof.
 intros u v tm Huv Hu Hv [HW|HD].
 - left; apply (proj1 (window_bound_swap u v tm B wait_width Hu Hv)); exact HW.
 - right; exact (Deferred_swap D u v tm Huv Hu Hv HD).
Qed.
Lemma decided_unmirror : forall tm, Decided (mirror_tm tm) -> Decided tm.
Proof.
 intros tm [HW|HD].
 - left; apply (proj1 (window_bound_mirror tm B wait_width)); exact HW.
 - right; exact (Deferred_mirror D tm HD).
Qed.

(** A halted completion has no observations at or after B. This covers
    the case where the last reached hole is left undefined. *)
Lemma halt_le_window : forall tm tm0 n q tp,
 TM_le tm tm0 -> stepn tm n InitES = Some (q,tp) ->
 tm0 q (t_head tp) = None -> S n <= B -> WindowBound tm0 B wait_width.
Proof.
 intros tm tm0 n q tp Hle Hn Hhalt HB q0 (t&Ht&c&HC&_).
 assert (Hnone : stepn tm0 (n + S (t-n-1)) InitES = None).
 { rewrite stepn_add, (TM_le_stepn tm tm0 n InitES (q,tp) Hle Hn).
   simpl; rewrite Hhalt; reflexivity. }
 replace (n+S (t-n-1)) with t in Hnone by lia.
 rewrite Hnone in HC; discriminate.
Qed.
Lemma node_decided_swap_unused : forall tm s i w d u v,
  tm s i = None ->
  ~ UnusedState tm s ->
  UnusedState tm u ->
  UnusedState tm v ->
  u <> v ->
  NodeDecided (TM_upd tm s i (Some (mkTrans w d v))) ->
  NodeDecided (TM_upd tm s i (Some (mkTrans w d u))).
Proof.
  intros tm s i w d u v Hhole Hused Hu Hv Huv Hnd tm0 Hle.
  assert (HuA : u <> StA) by (destruct Hu as (_ & _ & HA); exact HA).
  assert (HvA : v <> StA) by (destruct Hv as (_ & _ & HA); exact HA).
  apply (decided_unswap u v tm0 Huv HuA HvA).
  apply Hnd.
  rewrite <- (TM_swap_upd_unused tm s i w d u v Hhole Hused Hu Hv Huv).
  apply TM_le_swap; assumption.
Qed.

Lemma node_expand_spec : forall tm p n s tp,
  stepn tm n InitES = Some (s, tp) ->
  tm s (t_head tp) = None ->
  S n <= B ->
  UnusedState_ptr tm p ->
  (forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) -> Node_WF x') /\
  ((forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) ->
               NodeDecided (node_tm x')) ->
   NodeDecided tm).
Proof.
  intros tm p n s tp Hstep Hhole HB Hp.
  pose proof (stepn_reached_used tm n s tp Hstep) as Hused.
  split.
  - (* children well-formed *)
    intros x' Hin.
    unfold node_expand in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (tr & <- & Hin).
    apply filter_In in Hin.
    destruct Hin as [_ Hok].
    unfold Node_WF; simpl.
    rewrite TM_upd'_spec.
    apply UnusedState_ptr_upd; assumption.
  - (* children decided -> node decided *)
    intros Hch tm0 Hle.
    destruct (tm0 s (t_head tp)) as [tr|] eqn:E0.
    + (* the completion continues: covered by a child, up to a swap *)
      pose proof (TM_le_upd tm tm0 s (t_head tp) tr Hle E0) as Hle'.
      destruct tr as [w d nx].
      destruct (trans_ok p (mkTrans w d nx)) eqn:Eok.
      * (* in-range target: literally a child *)
        refine (Hch (mkNode (TM_upd' tm s (t_head tp) (Some (mkTrans w d nx)))
                            (ptr_after p nx)) _ tm0 _).
        -- unfold node_expand.
           apply in_map_iff.
           exists (mkTrans w d nx).
           split; [reflexivity|].
           apply filter_In.
           split; [apply all_trans_spec | exact Eok].
        -- simpl. rewrite TM_upd'_spec. exact Hle'.
      * (* beyond-pointer target: swap with the pointer state *)
        destruct p as [p0|]; simpl in Eok; [|discriminate].
        apply Nat.leb_gt in Eok.
        simpl in Hp.
        assert (Hnx : UnusedState tm nx) by (apply Hp; simpl; lia).
        assert (Hp0 : UnusedState tm p0) by (apply Hp; simpl; lia).
        assert (Hnep : nx <> p0)
          by (intro E; subst; lia).
        assert (Hok' : trans_ok (Some p0) (mkTrans w d p0) = true)
          by (simpl; apply Nat.leb_refl).
        refine (node_decided_swap_unused tm s (t_head tp) w d nx p0
                  Hhole Hused Hnx Hp0 Hnep _ tm0 Hle').
        refine (fun tmx Hx => Hch (mkNode (TM_upd' tm s (t_head tp) (Some (mkTrans w d p0)))
                            (ptr_after (Some p0) p0)) _ tmx _).
        -- unfold node_expand.
           apply in_map_iff.
           exists (mkTrans w d p0).
           split; [reflexivity|].
           apply filter_In.
           split; [apply all_trans_spec | exact Hok'].
        -- simpl. rewrite TM_upd'_spec. exact Hx.
    + (* the completion also halts here: score bounded by S n *)
      left.
      exact (halt_le_window tm tm0 n s tp Hle Hstep E0 HB).
Qed.


(** Reuse the old result tags solely as queue instructions. Every nonhalting
    leaf tag now requires the quantitative waiting property explicitly. *)
Definition QHDecider_WF (f : QHDecider) : Prop := forall tm,
 match f tm with
 | R_Halt s i => exists n tp,
     stepn tm n InitES = Some (s,tp) /\ t_head tp = i /\
     tm s i = None /\ S n <= B
 | R_NeverQH | R_QH | R_Leaf => NonHalt tm /\ WindowBound tm B wait_width
 | R_Deferred => In tm D
 | R_Unknown => True
 end.

Definition SearchQueue_WF (q : SearchQueue) (x0 : TNF_Node) : Prop :=
 let (q1,q2) := q in
 (forall x, In x (q1++q2) -> Node_WF x) /\
 ((forall x, In x (q1++q2) -> NodeDecided (node_tm x)) -> NodeDecided (node_tm x0)).
Lemma SearchQueue_upd_spec : forall q x0 f,
  SearchQueue_WF q x0 ->
  QHDecider_WF f ->
  SearchQueue_WF (SearchQueue_upd q f) x0.
Proof.
  intros [q1 q2] x0 f Hq Hf.
  destruct q1 as [| h t]; [exact Hq |].
  destruct Hq as [Hwf Hdec].
  simpl.
  specialize (Hf (node_tm h)).
  destruct (f (node_tm h)) eqn:Ef.
  - (* halt: expand *)
    destruct Hf as (n & tp & Hstep & Hhead & Hhole & HB).
    subst i.
    destruct h as [tm p].
    simpl in *.
    pose proof (node_expand_spec tm p n s tp Hstep Hhole HB
                  (Hwf (mkNode tm p) (or_introl eq_refl))) as [Hexp_wf Hexp_dec].
    split.
    + intros x Hin.
      rewrite in_app_iff in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [[Hin | Hin] | Hin].
      * apply Hexp_wf; exact Hin.
      * apply Hwf. simpl. rewrite in_app_iff. tauto.
      * apply Hwf. simpl. rewrite in_app_iff. tauto.
    + intros H.
      apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * simpl. apply Hexp_dec.
        intros x' Hin'. apply H.
        rewrite in_app_iff. rewrite in_app_iff. tauto.
      * apply H.
        rewrite in_app_iff. rewrite in_app_iff.
        rewrite in_app_iff in Hin. tauto.
  - (* every leaf requires a numerical window *)
    destruct Hf as (Hnh & Hb).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* QH leaf *)
    destruct Hf as (Hnh & Hb).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* undifferentiated leaf *)
    destruct Hf as (Hnh & Hb).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* deferred leaf *)
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_deferred; exact Hf.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* unknown: push to the back queue *)
    split.
    + intros x Hin. apply Hwf.
      simpl. rewrite in_app_iff. simpl.
      rewrite in_app_iff in Hin. simpl in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. apply H.
      simpl in Hin. rewrite in_app_iff in Hin.
      rewrite in_app_iff. simpl. tauto.
Qed.

Lemma SearchQueue_init_spec : forall x0,
  Node_WF x0 -> SearchQueue_WF (SearchQueue_init x0) x0.
Proof.
  intros x0 H.
  split.
  - intros x [<- | []]. exact H.
  - intros Hd. apply Hd. left. reflexivity.
Qed.

Lemma SearchQueue_upds_spec : forall n q x0 f,
  SearchQueue_WF q x0 ->
  QHDecider_WF f ->
  SearchQueue_WF (SearchQueue_upds q f n) x0.
Proof.
  induction n; intros q x0 f Hq Hf; simpl.
  - destruct (fst q); [exact Hq | apply SearchQueue_upd_spec; assumption].
  - destruct (fst q); [exact Hq |].
    apply IHn; [apply IHn|]; assumption.
Qed.

(** the census closes when the queue empties *)
Lemma SearchQueue_empty_decided : forall x0,
  SearchQueue_WF ([], []) x0 -> NodeDecided (node_tm x0).
Proof.
  intros x0 [_ Hdec].
  apply Hdec.
  intros x [].
Qed.

(** mirror transfer for whole nodes (used at the root, where the
    first-move-left children are covered by their mirrors) *)
Lemma node_decided_mirror : forall tm,
  NodeDecided (mirror_tm tm) -> NodeDecided tm.
Proof.
  intros tm H tm0 Hle.
  apply decided_unmirror.
  apply H.
  apply TM_le_mirror; exact Hle.
Qed.


(** Emptying a certified queue decides every completion of its root. *)
Theorem search_closes_root : forall x0 f n,
 Node_WF x0 -> QHDecider_WF f ->
 SearchQueue_upds (SearchQueue_init x0) f n = ([],[]) ->
 NodeDecided (node_tm x0).
Proof.
 intros x0 f n HW HF HE.
 pose proof (SearchQueue_upds_spec n (SearchQueue_init x0) x0 f
   (SearchQueue_init_spec x0 HW) HF) as HQ.
 rewrite HE in HQ; apply SearchQueue_empty_decided; exact HQ.
Qed.
(** Residual representatives must also control their completions; their
    nonhalting proofs make the existing deferred orbit safe for waiting. *)
Lemma deferred_wait :
 (forall h, In h D -> NonHalt h /\ WindowBound h B wait_width) ->
 forall tm, Deferred D tm -> WindowBound tm B wait_width.
Proof.
 intros HD tm H; induction H as [h tm Hin Hle|u v tm Huv Hu Hv Hdef IH|tm Hdef IH].
 - destruct (HD h Hin) as [Hnh HW].
   apply (proj2 (window_bound_completion h tm B wait_width Hnh Hle)); exact HW.
 - apply (proj1 (window_bound_swap u v tm B wait_width Hu Hv)); exact IH.
 - apply (proj1 (window_bound_mirror tm B wait_width)); exact IH.
Qed.

Theorem node_decided_no_residual :
 (forall h, In h D -> NonHalt h /\ WindowBound h B wait_width) ->
 forall tm, NodeDecided tm -> forall tm', TM_le tm tm' -> WindowBound tm' B wait_width.
Proof.
 intros HD tm H tm' Hle; destruct (H tm' Hle) as [HW|HR]; [exact HW|].
 apply (deferred_wait HD tm'); exact HR.
Qed.

End WaitingCensus.

Print Assumptions search_closes_root.
