(** * CensusTr/RunTr_Split: the frontier split, kernel-checked.

    The transition-level census theorem needs the WHOLE TNF tree walked
    to an empty queue under [decider_tr] with the frozen deferred list
    -- one computation far too large for a single [Qed].  The state
    census split it by hand: per-grandchild roots ([q_gsub]), further
    hand-split heavy subtrees ([Run_Split2], the [Run_Split_<tag>]
    files), each with its own well-formedness lemma.

    This file splits the SAME way the parallel collection walk does
    (WalkTr_Frontier.v): open the tree with [SearchQueue_levels] under
    the halt-only decider, then walk every frontier node's subtree
    separately.  Two lemmas make that a proof rather than bookkeeping:

    - [SearchQueue_level_spec_tr]: a level expansion preserves
      [SearchQueue_WF_Tr] under any [QHDeciderTr_WF] decider -- the
      same case analysis as [SearchQueue_upd_spec_tr], applied to
      every front node in one round instead of to the head.
    - [frontier_decided_tr]: if a well-formed queue's nodes each walk
      to an empty queue on their own, the root is decided.

    The units are then generated (tools/censustr/gen_walk_units.py):
    unit [i] of [N] certifies, by one native computation, that every
    frontier node whose index is [i] modulo [N] empties within [ITER]
    successor rounds ([unit_ok]); [units_cover_tr] turns the [N] unit
    facts into the theorem.  Round-robin by index is the collection
    walk's own dealing, so the units cost what its shards cost. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import TNF_QHTr DecideTr RunTr.
Import ListNotations.

Set Default Goal Selector "!".

(** ** A level expansion preserves well-formedness *)

Definition qnodes (q : SearchQueue) : list TNF_Node := fst q ++ snd q.

Lemma qnodes_push_front : forall l q x,
  In x (qnodes (l ++ fst q, snd q)) <-> In x l \/ In x (qnodes q).
Proof.
  intros l [q1 q2] x. unfold qnodes. simpl.
  rewrite <- app_assoc, !in_app_iff. tauto.
Qed.

Lemma qnodes_push_back : forall h q x,
  In x (qnodes (fst q, h :: snd q)) <-> h = x \/ In x (qnodes q).
Proof.
  intros h [q1 q2] x. unfold qnodes. simpl.
  rewrite !in_app_iff. simpl. tauto.
Qed.

(** the fold body of [SearchQueue_level], named so the induction below
    can talk about it *)
Definition level_step (f : QHDecider) (h : TNF_Node) (acc : SearchQueue)
  : SearchQueue :=
  match f (node_tm h) with
  | R_Halt s i => (node_expand h s i ++ fst acc, snd acc)
  | R_NeverQH | R_QH | R_Leaf | R_Deferred => acc
  | R_Unknown => (fst acc, h :: snd acc)
  end.

Lemma SearchQueue_level_fold : forall f q,
  SearchQueue_level f q = fold_right (level_step f) ([], snd q) (fst q).
Proof. intros f [q1 q2]. reflexivity. Qed.

(** the invariant carried through the fold: every node of the result
    is well-formed, and deciding every node of the result decides
    every node of the input list and of the accumulator *)
Lemma level_fold_spec_tr : forall f l acc,
  QHDeciderTr_WF B_tr D_tr f ->
  (forall x, In x l -> Node_WF x) ->
  (forall x, In x (qnodes acc) -> Node_WF x) ->
  (forall x, In x (qnodes (fold_right (level_step f) acc l)) -> Node_WF x) /\
  ((forall x, In x (qnodes (fold_right (level_step f) acc l)) ->
              NodeDecidedTr B_tr D_tr (node_tm x)) ->
   (forall x, In x l -> NodeDecidedTr B_tr D_tr (node_tm x)) /\
   (forall x, In x (qnodes acc) -> NodeDecidedTr B_tr D_tr (node_tm x))).
Proof.
  intros f l acc Hf.
  induction l as [| h t IH]; intros Hl Hacc.
  - simpl. split; [exact Hacc |].
    intros Hd. split; [intros x [] | exact Hd].
  - assert (Hh : Node_WF h) by (apply Hl; left; reflexivity).
    assert (Ht : forall x, In x t -> Node_WF x)
      by (intros x Hx; apply Hl; right; exact Hx).
    destruct (IH Ht Hacc) as [Hwf' Hdec'].
    set (r' := fold_right (level_step f) acc t) in *.
    change (fold_right (level_step f) acc (h :: t)) with (level_step f h r').
    unfold level_step.
    specialize (Hf (node_tm h)).
    destruct (f (node_tm h)) eqn:Ef.
    + (* halt: expand h in front of r' *)
      destruct Hf as (n & tp & Hstep & Hhead & Hhole & HB).
      subst i.
      destruct h as [tm p].
      pose proof (node_expand_tr_spec B_tr D_tr tm p n s tp Hstep Hhole HB Hh)
        as [Hexp_wf Hexp_dec].
      split.
      * intros x Hin. apply qnodes_push_front in Hin.
        destruct Hin as [Hin | Hin]; [apply Hexp_wf | apply Hwf']; exact Hin.
      * intros Hd.
        assert (Hd' : forall x, In x (qnodes r') ->
                      NodeDecidedTr B_tr D_tr (node_tm x)).
        { intros x Hx. apply Hd. apply qnodes_push_front. right; exact Hx. }
        destruct (Hdec' Hd') as [Hdt Hda].
        split; [| exact Hda].
        intros x [<- | Hx]; [| apply Hdt; exact Hx].
        apply Hexp_dec.
        intros x' Hx'. apply Hd. apply qnodes_push_front. left; exact Hx'.
    + (* never-QH leaf: h dropped *)
      split; [exact Hwf' |].
      intros Hd. destruct (Hdec' Hd) as [Hdt Hda].
      split; [| exact Hda].
      intros x [<- | Hx]; [| apply Hdt; exact Hx].
      apply node_decided_tr_neverqh; exact Hf.
    + (* QH leaf *)
      destruct Hf as (Hnh & Hb & _).
      split; [exact Hwf' |].
      intros Hd. destruct (Hdec' Hd) as [Hdt Hda].
      split; [| exact Hda].
      intros x [<- | Hx]; [| apply Hdt; exact Hx].
      apply node_decided_tr_leaf; assumption.
    + (* undifferentiated leaf *)
      destruct Hf as (Hnh & Hb).
      split; [exact Hwf' |].
      intros Hd. destruct (Hdec' Hd) as [Hdt Hda].
      split; [| exact Hda].
      intros x [<- | Hx]; [| apply Hdt; exact Hx].
      apply node_decided_tr_leaf; assumption.
    + (* deferred leaf *)
      split; [exact Hwf' |].
      intros Hd. destruct (Hdec' Hd) as [Hdt Hda].
      split; [| exact Hda].
      intros x [<- | Hx]; [| apply Hdt; exact Hx].
      apply node_decided_tr_deferred; exact Hf.
    + (* unknown: h goes to the back of r' *)
      split.
      * intros x Hin. apply qnodes_push_back in Hin.
        destruct Hin as [<- | Hin]; [exact Hh | apply Hwf'; exact Hin].
      * intros Hd.
        assert (Hd' : forall x, In x (qnodes r') ->
                      NodeDecidedTr B_tr D_tr (node_tm x)).
        { intros x Hx. apply Hd. apply qnodes_push_back. right; exact Hx. }
        destruct (Hdec' Hd') as [Hdt Hda].
        split; [| exact Hda].
        intros x [<- | Hx]; [| apply Hdt; exact Hx].
        apply Hd. apply qnodes_push_back. left; reflexivity.
Qed.

Lemma SearchQueue_level_spec_tr : forall f q x0,
  SearchQueue_WF_Tr B_tr D_tr q x0 ->
  QHDeciderTr_WF B_tr D_tr f ->
  SearchQueue_WF_Tr B_tr D_tr (SearchQueue_level f q) x0.
Proof.
  intros f [q1 q2] x0 [Hwf Hdec] Hf.
  rewrite SearchQueue_level_fold. simpl (fst _). simpl (snd _).
  assert (Hl : forall x, In x q1 -> Node_WF x)
    by (intros x Hx; apply Hwf; rewrite in_app_iff; left; exact Hx).
  assert (Hacc : forall x, In x (qnodes ([], q2)) -> Node_WF x)
    by (intros x Hx; apply Hwf; rewrite in_app_iff; right; exact Hx).
  destruct (level_fold_spec_tr f q1 ([], q2) Hf Hl Hacc) as [Hwf' Hdec'].
  destruct (fold_right (level_step f) ([], q2) q1) as [r1 r2].
  split.
  - intros x Hx. apply Hwf'. exact Hx.
  - intros Hd.
    destruct (Hdec' Hd) as [Hd1 Hd2].
    apply Hdec.
    intros x Hx. rewrite in_app_iff in Hx.
    destruct Hx as [Hx | Hx]; [apply Hd1; exact Hx | apply Hd2; exact Hx].
Qed.

Lemma SearchQueue_levels_spec_tr : forall f n q x0,
  SearchQueue_WF_Tr B_tr D_tr q x0 ->
  QHDeciderTr_WF B_tr D_tr f ->
  SearchQueue_WF_Tr B_tr D_tr (SearchQueue_levels f n q) x0.
Proof.
  intros f n q x0 Hq Hf.
  induction n as [| n IH]; simpl.
  - exact Hq.
  - apply SearchQueue_level_spec_tr; assumption.
Qed.

(** ** From per-node walks to the root *)

Lemma q_iter_from_tr : forall n q x0,
  SearchQueue_WF_Tr B_tr D_tr q x0 ->
  SearchQueue_WF_Tr B_tr D_tr (Nat.iter n q_suc_tr q) x0.
Proof.
  induction n as [| n IH]; intros q x0 Hq; simpl.
  - exact Hq.
  - apply SearchQueue_upds_spec_tr; [apply IH; exact Hq | exact decider_tr_WF].
Qed.

Lemma node_walk_decided_tr : forall h n,
  Node_WF h ->
  Nat.iter n q_suc_tr ([h], []) = ([], []) ->
  NodeDecidedTr B_tr D_tr (node_tm h).
Proof.
  intros h n Hwf Hempty.
  pose proof (q_iter_from_tr n ([h], []) h
                (SearchQueue_init_spec_tr B_tr D_tr h Hwf)) as HWF.
  rewrite Hempty in HWF.
  exact (SearchQueue_empty_decided_tr B_tr D_tr h HWF).
Qed.

Lemma frontier_decided_tr : forall q x0,
  SearchQueue_WF_Tr B_tr D_tr q x0 ->
  (forall h, In h (qnodes q) ->
             exists n, Nat.iter n q_suc_tr ([h], []) = ([], [])) ->
  NodeDecidedTr B_tr D_tr (node_tm x0).
Proof.
  intros [q1 q2] x0 [Hwf Hdec] Hwalk.
  apply Hdec.
  intros x Hx.
  destruct (Hwalk x Hx) as [n Hn].
  exact (node_walk_decided_tr x n (Hwf x Hx) Hn).
Qed.

(** ** The frontier and its units *)

Definition FRONTIER_LEVELS_TR : nat := 3.

Definition frontier_tr : SearchQueue :=
  SearchQueue_levels decider_tr_fast FRONTIER_LEVELS_TR q_0_tr.

Definition frontier_nodes_tr : list TNF_Node := qnodes frontier_tr.

Lemma frontier_tr_WF : SearchQueue_WF_Tr B_tr D_tr frontier_tr root.
Proof.
  apply SearchQueue_levels_spec_tr; [exact q_0_tr_WF | exact decider_tr_fast_WF].
Qed.

(** successor rounds per unit: the collection shards' own budget
    (gen_walk_shards.py); iterating past exhaustion is a no-op *)
Definition ITER_TR : nat := 4096.

Definition queue_empty_b (q : SearchQueue) : bool :=
  match q with ([], []) => true | _ => false end.

Lemma queue_empty_b_spec : forall q, queue_empty_b q = true -> q = ([], []).
Proof. intros [[|a l1] [|b l2]] H; simpl in H; congruence. Qed.

(** unit [i] of [N]: every node at index [j] (counting from the given
    offset) with [j mod N = i] walks to an empty queue *)
Fixpoint unit_ok (N i j : nat) (l : list TNF_Node) : bool :=
  match l with
  | [] => true
  | h :: t =>
      (if Nat.eqb (j mod N) i
       then queue_empty_b (Nat.iter ITER_TR q_suc_tr ([h], []))
       else true)
      && unit_ok N i (S j) t
  end.

(** the one-step equation, so no tactic ever has to [simpl] a term
    containing [Nat.iter ITER_TR] *)
Lemma unit_ok_cons : forall N i j h t,
  unit_ok N i j (h :: t) =
  (if Nat.eqb (j mod N) i
   then queue_empty_b (Nat.iter ITER_TR q_suc_tr ([h], []))
   else true)
  && unit_ok N i (S j) t.
Proof. reflexivity. Qed.

Lemma unit_ok_spec : forall N l j h,
  0 < N ->
  In h l ->
  (forall i, i < N -> unit_ok N i j l = true) ->
  Nat.iter ITER_TR q_suc_tr ([h], []) = ([], []).
Proof.
  intros N l.
  induction l as [| a t IH]; intros j h HN Hin Hu; [destruct Hin |].
  assert (HN0 : N <> 0) by lia.
  destruct Hin as [<- | Hin].
  - specialize (Hu (j mod N) (Nat.mod_upper_bound j N HN0)).
    rewrite unit_ok_cons in Hu. apply andb_prop in Hu as [Hu _].
    rewrite Nat.eqb_refl in Hu.
    exact (queue_empty_b_spec _ Hu).
  - apply (IH (S j) h HN Hin).
    intros i Hi. specialize (Hu i Hi).
    rewrite unit_ok_cons in Hu. apply andb_prop in Hu as [_ Hu]. exact Hu.
Qed.

(** the [N] unit facts cover the frontier, hence the root *)
Theorem census_tr_of_units : forall N,
  0 < N ->
  (forall i, i < N -> unit_ok N i 0 frontier_nodes_tr = true) ->
  forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm.
Proof.
  intros N HN Hunits tm.
  assert (Hroot : NodeDecidedTr B_tr D_tr (node_tm root)).
  { apply (frontier_decided_tr frontier_tr root frontier_tr_WF).
    intros h Hh. exists ITER_TR.
    exact (unit_ok_spec N frontier_nodes_tr 0 h HN Hh Hunits). }
  exact (Hroot tm (TM_le_TM0 (node_tm root) tm (fun _ _ => eq_refl))).
Qed.
