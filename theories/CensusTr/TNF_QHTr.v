(** * CensusTr/TNF_QHTr: the TNF census core at transition level.

    The instruction-level (transition-level) fork of Census/TNF_QH.v.
    The design split (SCOPING_INSTR.md section 6): the SYNTAX machinery
    -- [TM_le], [TM_upd], [TM_swap], unused-state pointers, [TNF_Node],
    [node_expand], [QHResult], the [SearchQueue] computation -- is
    predicate-free and REUSED BY IMPORT from TNF_QH.v, so a
    transition-level walk runs the exact same [Nat.iter]/[SearchQueue]
    computation as the state-level one.  What forks is the soundness
    layer: the bound predicate ([QHBoundTr]), its transport lemmas
    (completion / swap / mirror), and the [_WF] contracts for deciders
    and queues.

    Nothing in the state-level development is touched; this file only
    imports it. *)

From Coq Require Import Arith Lia Bool List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Set Default Goal Selector "!".

(** ** The transition-level score bound

    [QHBoundTr B tm]: every instruction that is eventually quiet made
    its last fire before configuration index [B].  Vacuous for
    transition-level never-quasihalting machines; equal to the score
    bound for transition-level quasihalting ones. *)

Definition QHBoundTr (B : nat) (tm : TM) : Prop :=
  forall t s, QuietAfterTr tm t s -> S s <= B.

Lemma qhboundtr_mono : forall B B' tm,
  B <= B' -> QHBoundTr B tm -> QHBoundTr B' tm.
Proof.
  intros B B' tm Hb H t s Hq.
  specialize (H t s Hq). lia.
Qed.

Lemma neverqhtr_qhboundtr : forall B tm,
  NeverQuasiHaltsTr tm -> QHBoundTr B tm.
Proof.
  intros B tm H t s [Hf Hq].
  destruct (H t (ex_intro _ s Hf) (S s)) as (n & Hn & Hfn).
  exfalso. apply (Hq n); [lia | exact Hfn].
Qed.

(** the transition bound implies the state bound: a quiet state's last
    visit is witnessed by a quiet instruction at the same index *)
Lemma qhboundtr_qhbound : forall B tm,
  QHBoundTr B tm -> QHBound B tm.
Proof.
  intros B tm H q s [Hvis Hq].
  apply visits_fires in Hvis.
  destruct Hvis as (a & Hf).
  apply (H (q, a) s).
  split; [exact Hf|].
  intros n Hn Hfn.
  exact (Hq n Hn (fires_visits tm q a n Hfn)).
Qed.

(** ** Completion transfer (the don't-care argument) *)

Lemma fires_le : forall tm tm' t n,
  NonHalt tm -> TM_le tm tm' ->
  (FiresAt tm' t n <-> FiresAt tm t n).
Proof.
  intros tm tm' t n Hnh Hle.
  destruct (stepn tm n InitES) as [c|] eqn:Ec;
    [| exfalso; exact (Hnh n Ec)].
  pose proof (TM_le_stepn tm tm' n InitES c Hle Ec) as Ec'.
  split; intros (c0 & H0 & Ht).
  - rewrite Ec' in H0. injection H0 as <-.
    exists c. split; [exact Ec | exact Ht].
  - rewrite Ec in H0. injection H0 as <-.
    exists c. split; [exact Ec' | exact Ht].
Qed.

Lemma quiet_tr_le : forall tm tm' t s,
  NonHalt tm -> TM_le tm tm' ->
  (QuietAfterTr tm' t s <-> QuietAfterTr tm t s).
Proof.
  intros tm tm' t s Hnh Hle.
  unfold QuietAfterTr.
  split; intros [Hf Hq]; split.
  - apply (fires_le tm tm' t s Hnh Hle); exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), (fires_le tm tm' t n Hnh Hle), Hv.
  - apply (fires_le tm tm' t s Hnh Hle); exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), (fires_le tm tm' t n Hnh Hle), Hv.
Qed.

Lemma qhboundtr_le : forall B tm tm',
  NonHalt tm -> QHBoundTr B tm -> TM_le tm tm' -> QHBoundTr B tm'.
Proof.
  intros B tm tm' Hnh H Hle t s Hq.
  apply (H t s), (quiet_tr_le tm tm' t s Hnh Hle), Hq.
Qed.

(** ** The halting side: after an undefined transition is reached at
    index [n], no configuration exists, so every instruction is quiet
    by [n]. *)

Lemma halt_le_qhboundtr : forall B tm tm0 n s tp,
  TM_le tm tm0 ->
  stepn tm n InitES = Some (s, tp) ->
  tm0 s (t_head tp) = None ->
  S n <= B ->
  QHBoundTr B tm0.
Proof.
  intros B tm tm0 n s tp Hle Hn Hhalt HB t s0 [Hf _].
  destruct Hf as (c & Hc & _).
  assert (Hno : forall k, 1 <= k -> stepn tm0 (n + k) InitES = None).
  { intros k Hk.
    rewrite stepn_add.
    rewrite (TM_le_stepn tm tm0 n InitES (s, tp) Hle Hn).
    destruct k; [lia|].
    simpl. rewrite Hhalt. reflexivity. }
  destruct (le_lt_dec s0 n) as [Hle0 | Hgt]; [lia|].
  exfalso.
  specialize (Hno (s0 - n) ltac:(lia)).
  replace (n + (s0 - n)) with s0 in Hno by lia.
  rewrite Hno in Hc. discriminate.
Qed.

(** ** Swap transfer

    [es_swap] touches only the state component, so an instruction's
    symbol rides along untouched. *)

Definition Instr_swap (u v : St) (t : Instr) : Instr :=
  (St_swap u v (fst t), snd t).

Lemma Instr_swap_swap : forall u v t, Instr_swap u v (Instr_swap u v t) = t.
Proof.
  intros u v [q a]. unfold Instr_swap; simpl.
  rewrite St_swap_swap. reflexivity.
Qed.

Lemma instr_of_es_swap : forall u v c,
  instr_of (es_swap u v c) = Instr_swap u v (instr_of c).
Proof. intros u v [q tp]. reflexivity. Qed.

Lemma fires_swap : forall u v tm t n,
  u <> StA -> v <> StA ->
  (FiresAt (TM_swap u v tm) t n <-> FiresAt tm (Instr_swap u v t) n).
Proof.
  intros u v tm t n HuA HvA. unfold FiresAt.
  rewrite stepn_swap, es_swap_init by assumption.
  destruct (stepn tm n InitES) as [c|]; simpl.
  - split.
    + intros (c0 & H0 & Ht). injection H0 as <-.
      exists c. split; [reflexivity|].
      rewrite instr_of_es_swap in Ht.
      rewrite <- Ht, Instr_swap_swap. reflexivity.
    + intros (c0 & H0 & Ht). injection H0 as <-.
      eexists. split; [reflexivity|].
      rewrite instr_of_es_swap, Ht, Instr_swap_swap. reflexivity.
  - split; intros (c0 & H0 & _); discriminate.
Qed.

Lemma quiet_tr_swap : forall u v tm t s,
  u <> StA -> v <> StA ->
  (QuietAfterTr (TM_swap u v tm) t s <-> QuietAfterTr tm (Instr_swap u v t) s).
Proof.
  intros u v tm t s HuA HvA. unfold QuietAfterTr.
  split; intros [Hf Hq]; split.
  - apply (fires_swap u v tm t s HuA HvA); exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), (fires_swap u v tm t n HuA HvA), Hv.
  - apply (fires_swap u v tm t s HuA HvA); exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), (fires_swap u v tm t n HuA HvA), Hv.
Qed.

Lemma qhboundtr_swap : forall u v B tm,
  u <> StA -> v <> StA ->
  QHBoundTr B tm -> QHBoundTr B (TM_swap u v tm).
Proof.
  intros u v B tm HuA HvA H t s Hq.
  apply (H (Instr_swap u v t) s), (quiet_tr_swap u v tm t s HuA HvA), Hq.
Qed.

(** ** Mirror transfer: [mirror_tape] keeps the head cell, so an
    instruction fires in the mirror iff it fires in the original. *)

Lemma instr_of_mirror : forall c, instr_of (mirror_es c) = instr_of c.
Proof. intros [q [l h r]]. reflexivity. Qed.

Lemma mirror_fires : forall tm t n,
  FiresAt (mirror_tm tm) t n <-> FiresAt tm t n.
Proof.
  intros tm t n; unfold FiresAt; split.
  - intros (c & Hc & Ht).
    rewrite mirror_stepn_init in Hc.
    destruct (stepn tm n InitES) as [c'|] eqn:E; [|discriminate].
    injection Hc as <-.
    exists c'. split; [reflexivity|].
    rewrite instr_of_mirror in Ht. exact Ht.
  - intros (c & Hc & Ht).
    exists (mirror_es c). split.
    + rewrite mirror_stepn_init, Hc. reflexivity.
    + rewrite instr_of_mirror. exact Ht.
Qed.

Lemma quiet_tr_mirror : forall tm t s,
  QuietAfterTr (mirror_tm tm) t s <-> QuietAfterTr tm t s.
Proof.
  intros tm t s. unfold QuietAfterTr.
  split; intros [Hf Hq]; split.
  - apply mirror_fires; exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), mirror_fires, Hv.
  - apply mirror_fires; exact Hf.
  - intros n Hn Hv. apply (Hq n Hn), mirror_fires, Hv.
Qed.

Lemma qhboundtr_mirror : forall B tm,
  QHBoundTr B (mirror_tm tm) -> QHBoundTr B tm.
Proof.
  intros B tm H t s Hq.
  apply (H t s), quiet_tr_mirror, Hq.
Qed.

Lemma neverqhtr_mirror : forall tm,
  NeverQuasiHaltsTr (mirror_tm tm) -> NeverQuasiHaltsTr tm.
Proof.
  intros tm H t Hf N.
  assert (Hf' : FiredTr (mirror_tm tm) t).
  { destruct Hf as (n0 & Hf0). exists n0. apply mirror_fires. exact Hf0. }
  destruct (H t Hf' N) as (n & Hn & Hfn).
  exists n. split; [exact Hn | apply mirror_fires; exact Hfn].
Qed.

(** ** The transition-level census predicate

    [Deferred] is reused verbatim: the orbit construction is
    predicate-free, and any property invariant under completion, swap
    and mirror lifts over it -- [QHBoundTr] just proved to be one. *)

Section CensusTr.

Variable B : nat.          (** the global transition-score bound *)
Variable D : list TM.      (** the deferred list *)

Definition DecidedTr (tm : TM) : Prop := QHBoundTr B tm \/ Deferred D tm.

Definition NodeDecidedTr (tm : TM) : Prop :=
  forall tm', TM_le tm tm' -> DecidedTr tm'.

(** leaf discharge lemmas *)

Lemma node_decided_tr_leaf : forall tm,
  NonHalt tm -> QHBoundTr B tm -> NodeDecidedTr tm.
Proof.
  intros tm Hnh Hb tm' Hle.
  left. apply (qhboundtr_le B tm tm' Hnh Hb Hle).
Qed.

Lemma node_decided_tr_neverqh : forall tm,
  NeverQuasiHaltsTr tm -> NodeDecidedTr tm.
Proof.
  intros tm H.
  apply node_decided_tr_leaf.
  - apply never_qh_tr_nonhalt; exact H.
  - apply neverqhtr_qhboundtr; exact H.
Qed.

Lemma node_decided_tr_deferred : forall tm,
  In tm D -> NodeDecidedTr tm.
Proof.
  intros tm H tm' Hle.
  right. exact (Deferred_base D tm tm' H Hle).
Qed.

(** transfer of [DecidedTr] along swap/mirror *)

Lemma decided_tr_unswap : forall u v tm,
  u <> v -> u <> StA -> v <> StA ->
  DecidedTr (TM_swap u v tm) -> DecidedTr tm.
Proof.
  intros u v tm Huv HuA HvA [H | H].
  - left.
    pose proof (qhboundtr_swap u v B (TM_swap u v tm) HuA HvA H) as H'.
    rewrite (TM_swap_swap u v) in H'. exact H'.
  - right. exact (Deferred_swap D u v tm Huv HuA HvA H).
Qed.

Lemma decided_tr_unmirror : forall tm,
  DecidedTr (mirror_tm tm) -> DecidedTr tm.
Proof.
  intros tm [H | H].
  - left. apply qhboundtr_mirror; exact H.
  - right. exact (Deferred_mirror D tm H).
Qed.

(** the swap argument at expansion time, over the reused
    [TM_swap_upd_unused] *)

Lemma node_decided_tr_swap_unused : forall tm s i w d u v,
  tm s i = None ->
  ~ UnusedState tm s ->
  UnusedState tm u ->
  UnusedState tm v ->
  u <> v ->
  NodeDecidedTr (TM_upd tm s i (Some (mkTrans w d v))) ->
  NodeDecidedTr (TM_upd tm s i (Some (mkTrans w d u))).
Proof.
  intros tm s i w d u v Hhole Hused Hu Hv Huv Hnd tm0 Hle.
  assert (HuA : u <> StA) by (destruct Hu as (_ & _ & HA); exact HA).
  assert (HvA : v <> StA) by (destruct Hv as (_ & _ & HA); exact HA).
  apply (decided_tr_unswap u v tm0 Huv HuA HvA).
  apply Hnd.
  rewrite <- (TM_swap_upd_unused tm s i w d u v Hhole Hused Hu Hv Huv).
  apply TM_le_swap; assumption.
Qed.

(** children cover the node (the reused [node_expand], with the
    transition-level halting discharge at the leaf) *)

Lemma node_expand_tr_spec : forall tm p n s tp,
  stepn tm n InitES = Some (s, tp) ->
  tm s (t_head tp) = None ->
  S n <= B ->
  UnusedState_ptr tm p ->
  (forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) -> Node_WF x') /\
  ((forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) ->
               NodeDecidedTr (node_tm x')) ->
   NodeDecidedTr tm).
Proof.
  intros tm p n s tp Hstep Hhole HB Hp.
  pose proof (stepn_reached_used tm n s tp Hstep) as Hused.
  split.
  - intros x' Hin.
    unfold node_expand in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (tr & <- & Hin).
    apply filter_In in Hin.
    destruct Hin as [_ Hok].
    unfold Node_WF; simpl.
    rewrite TM_upd'_spec.
    apply UnusedState_ptr_upd; assumption.
  - intros Hch tm0 Hle.
    destruct (tm0 s (t_head tp)) as [tr|] eqn:E0.
    + pose proof (TM_le_upd tm tm0 s (t_head tp) tr Hle E0) as Hle'.
      destruct tr as [w d nx].
      destruct (trans_ok p (mkTrans w d nx)) eqn:Eok.
      * refine (Hch (mkNode (TM_upd' tm s (t_head tp) (Some (mkTrans w d nx)))
                            (ptr_after p nx)) _ tm0 _).
        -- unfold node_expand.
           apply in_map_iff.
           exists (mkTrans w d nx).
           split; [reflexivity|].
           apply filter_In.
           split; [apply all_trans_spec | exact Eok].
        -- simpl. rewrite TM_upd'_spec. exact Hle'.
      * destruct p as [p0|]; simpl in Eok; [|discriminate].
        apply Nat.leb_gt in Eok.
        simpl in Hp.
        assert (Hnx : UnusedState tm nx) by (apply Hp; simpl; lia).
        assert (Hp0 : UnusedState tm p0) by (apply Hp; simpl; lia).
        assert (Hnep : nx <> p0)
          by (intro E; subst; lia).
        assert (Hok' : trans_ok (Some p0) (mkTrans w d p0) = true)
          by (simpl; apply Nat.leb_refl).
        refine (node_decided_tr_swap_unused tm s (t_head tp) w d nx p0
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
    + left.
      exact (halt_le_qhboundtr B tm tm0 n s tp Hle Hstep E0 HB).
Qed.

(** ** The decider contract at transition level

    [QHResult] and the [SearchQueue] computation are REUSED: only the
    meaning of the verdicts changes. *)

Definition QHDeciderTr_WF (f : QHDecider) : Prop :=
  forall tm,
    match f tm with
    | R_Halt s i => exists n tp,
        stepn tm n InitES = Some (s, tp) /\ t_head tp = i /\
        tm s i = None /\ S n <= B
    | R_NeverQH => NeverQuasiHaltsTr tm
    | R_QH => NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm
    | R_Leaf => NonHalt tm /\ QHBoundTr B tm
    | R_Deferred => In tm D
    | R_Unknown => True
    end.

(** ** Queue soundness at transition level, over the reused
    [SearchQueue_upd] / [SearchQueue_upds] computation *)

Definition SearchQueue_WF_Tr (q : SearchQueue) (x0 : TNF_Node) : Prop :=
  let (q1, q2) := q in
  (forall x, In x (q1 ++ q2) -> Node_WF x) /\
  ((forall x, In x (q1 ++ q2) -> NodeDecidedTr (node_tm x)) ->
   NodeDecidedTr (node_tm x0)).

Lemma SearchQueue_upd_spec_tr : forall q x0 f,
  SearchQueue_WF_Tr q x0 ->
  QHDeciderTr_WF f ->
  SearchQueue_WF_Tr (SearchQueue_upd q f) x0.
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
    pose proof (node_expand_tr_spec tm p n s tp Hstep Hhole HB
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
  - (* never-QH (transition level) leaf *)
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_tr_neverqh; exact Hf.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* QH leaf *)
    destruct Hf as (Hnh & Hb & _).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_tr_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* undifferentiated leaf *)
    destruct Hf as (Hnh & Hb).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_tr_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* deferred leaf *)
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_tr_deferred; exact Hf.
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

Lemma SearchQueue_init_spec_tr : forall x0,
  Node_WF x0 -> SearchQueue_WF_Tr (SearchQueue_init x0) x0.
Proof.
  intros x0 H.
  split.
  - intros x [<- | []]. exact H.
  - intros Hd. apply Hd. left. reflexivity.
Qed.

Lemma SearchQueue_upds_spec_tr : forall n q x0 f,
  SearchQueue_WF_Tr q x0 ->
  QHDeciderTr_WF f ->
  SearchQueue_WF_Tr (SearchQueue_upds q f n) x0.
Proof.
  induction n; intros q x0 f Hq Hf; simpl.
  - destruct (fst q); [exact Hq | apply SearchQueue_upd_spec_tr; assumption].
  - destruct (fst q); [exact Hq |].
    apply IHn; [apply IHn|]; assumption.
Qed.

Lemma SearchQueue_empty_decided_tr : forall x0,
  SearchQueue_WF_Tr ([], []) x0 -> NodeDecidedTr (node_tm x0).
Proof.
  intros x0 [_ Hdec].
  apply Hdec.
  intros x [].
Qed.

Lemma node_decided_tr_mirror : forall tm,
  NodeDecidedTr (mirror_tm tm) -> NodeDecidedTr tm.
Proof.
  intros tm H tm0 Hle.
  apply decided_tr_unmirror.
  apply H.
  apply TM_le_mirror; exact Hle.
Qed.

End CensusTr.
