(** Quantitative finite-graph ranks for state waiting windows.

    A non-target node of rank zero may step directly to the target, so
    the general bound is [rank a + 1], not [rank a]. These results use
    the existing checked finite closure and rank gates. They do not
    turn unbounded tape measures or lexicographic counters into a
    finite-graph bound. No run is simulated to the cutoff [B]. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import NGram ExactClosure.
From BBBWait42 Require Import Spec.
Import ListNotations.

Section QuantitativeRanks.
  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).
  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_state : forall a c, covers a c -> a_state a = fst c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  (** Retain the step budget in the induction used by [Closure.rank_reach]. *)
  Lemma rank_reach_with_budget : forall Sl q rnk,
    closed_b A a_enc succs Sl = true ->
    rank_ok A a_state succs Sl q rnk = true ->
    forall r a c, rnk a < r -> In a Sl -> covers a c ->
    exists j c', j <= r /\ stepn tm j c = Some c' /\ fst c' = q.
  Proof.
    intros Sl q rnk Hcl Hro.
    induction r as [|r IH]; intros a c Hr HIn Hcov; [lia|].
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - apply st_eqb_spec in Eq.
      exists 0, c. repeat split; try lia; try reflexivity.
      rewrite <- (covers_state a c Hcov). exact Eq.
    - destruct (closed_step tm A a_enc succs covers a_enc_inj succs_sound
                  Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists 1, c'. split; [lia|]. split.
        * cbn [stepn]. rewrite Hstep. reflexivity.
        * rewrite <- (covers_state a' c' Hcov'). exact Eq'.
      + assert (Hlt : rnk a' < rnk a).
        { unfold rank_ok in Hro. rewrite forallb_forall in Hro.
          specialize (Hro a HIn). rewrite Eq, Es in Hro.
          rewrite forallb_forall in Hro. specialize (Hro a' HInl).
          unfold edge_ok in Hro. rewrite Eq' in Hro. simpl in Hro.
          apply Nat.ltb_lt. exact Hro. }
        destruct (IH a' c' ltac:(lia) HIn' Hcov')
          as (j & c'' & Hj & Hsteps & Hq).
        exists (S j), c''. split; [lia|]. split; [|exact Hq].
        cbn [stepn]. rewrite Hstep. exact Hsteps.
  Qed.

  Theorem rank_reach_bounded : forall Sl q rnk,
    closed_b A a_enc succs Sl = true ->
    rank_ok A a_state succs Sl q rnk = true ->
    forall a c, In a Sl -> covers a c ->
    exists j c', j <= S (rnk a) /\
      stepn tm j c = Some c' /\ fst c' = q.
  Proof.
    intros Sl q rnk Hcl Hro a c HIn Hcov.
    eapply rank_reach_with_budget; eauto.
  Qed.

  Theorem rank_find_bounded : forall Sl q rnk,
    closed_b A a_enc succs Sl = true ->
    rank_ok A a_state succs Sl q rnk = true ->
    forall a c m, In a Sl -> covers a c ->
    stepn tm m InitES = Some c ->
    exists n, m <= n /\ n <= m + S (rnk a) /\ VisitsAt tm q n.
  Proof.
    intros Sl q rnk Hcl Hro a c m HIn Hcov Hm.
    destruct (rank_reach_bounded Sl q rnk Hcl Hro a c HIn Hcov)
      as (j & c' & Hj & Hsteps & Hq).
    exists (m+j). repeat split; try lia.
    exists c'. split; [|exact Hq]. rewrite stepn_add, Hm. exact Hsteps.
  Qed.

  (** A checked closed tail can be advanced symbolically to any cutoff.
      The rank bound is uniform over the finite pool, rather than over
      unbounded concrete measure values. States not appearing in the
      pool cannot provide a future beep after the anchor. *)
  Theorem closed_tail_window_bound : forall Sl (ranks : St -> A -> nat)
      a0 c0' t B w,
    closed_b A a_enc succs Sl = true ->
    In a0 Sl -> covers a0 c0' ->
    stepn tm t InitES = Some c0' -> t <= B ->
    (forall q, appears A a_state Sl q = true ->
      rank_ok A a_state succs Sl q (ranks q) = true) ->
    (forall q a, appears A a_state Sl q = true -> In a Sl ->
      S (ranks q a) <= w) ->
    WindowBound tm B w.
  Proof.
    intros Sl ranks a0 c0' t B w Hcl HIn Hcov Hanchor Ht Hranks Hbound.
    intros q (u & Hu & cu & Hrun & Hq).
    assert (Htailu : stepn tm (u-t) c0' = Some cu).
    { replace u with (t+(u-t)) in Hrun by lia.
      rewrite stepn_add, Hanchor in Hrun. exact Hrun. }
    assert (Happ : appears A a_state Sl q = true).
    { rewrite <- Hq. eapply live_visited_appears; eauto. }
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj succs_sound
                Sl Hcl a0 c0' HIn Hcov (B-t))
      as (cB & aB & HstepsB & HInB & HcovB).
    assert (HrunB : stepn tm B InitES = Some cB).
    { replace B with (t+(B-t)) by lia. rewrite stepn_add, Hanchor. exact HstepsB. }
    destruct (rank_find_bounded Sl q (ranks q) Hcl (Hranks q Happ)
                aB cB B HInB HcovB HrunB)
      as (v & Hv & Hvb & Hvq).
    exists v. repeat split; auto. specialize (Hbound q aB Happ HInB). lia.
  Qed.
End QuantitativeRanks.

(** This gate accepts supplied ranks; rank synthesis remains untrusted. *)
Definition ranked_window_ok {A : Type} (a_state : A -> St)
    (succs : A -> option (list A)) (Sl : list A)
    (ranks : St -> A -> nat) (w : nat) : bool :=
  forallb (fun q =>
    if appears A a_state Sl q then
      rank_ok A a_state succs Sl q (ranks q) &&
      forallb (fun a => S (ranks q a) <=? w) Sl
    else true) all_St.

Lemma ranked_window_ok_sound : forall A a_state succs Sl ranks w,
  @ranked_window_ok A a_state succs Sl ranks w = true ->
  (forall q, appears A a_state Sl q = true ->
    rank_ok A a_state succs Sl q (ranks q) = true) /\
  (forall q a, appears A a_state Sl q = true -> In a Sl ->
    S (ranks q a) <= w).
Proof.
  intros A a_state succs Sl ranks w H.
  unfold ranked_window_ok in H. rewrite forallb_forall in H.
  assert (Hg : forall q, appears A a_state Sl q = true ->
    rank_ok A a_state succs Sl q (ranks q) = true /\
    forallb (fun a => S (ranks q a) <=? w) Sl = true).
  { intros q Happ. specialize (H q (all_St_complete q)).
    rewrite Happ in H. apply andb_true_iff. exact H. }
  split.
  - intros q Happ. exact (proj1 (Hg q Happ)).
  - intros q a Happ HIn. destruct (Hg q Happ) as [_ Hbound].
    rewrite forallb_forall in Hbound.
    apply Nat.leb_le. apply Hbound. exact HIn.
Qed.

Theorem ranked_window_ok_window_bound : forall tm A a_enc a_state succs covers,
  (forall x y, a_enc x = a_enc y -> x = y) ->
  (forall a c, covers a c -> a_state a = fst c) ->
  (forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False | None, _ => True end) ->
  forall Sl ranks a0 c0' t B w,
  closed_b A a_enc succs Sl = true ->
  In a0 Sl -> covers a0 c0' ->
  stepn tm t InitES = Some c0' -> t <= B ->
  ranked_window_ok a_state succs Sl ranks w = true ->
  WindowBound tm B w.
Proof.
  intros tm A a_enc a_state succs covers Hinj Hstate Hsucc
    Sl ranks a0 c0' t B w Hcl HIn Hcov Hanchor Ht Hgate.
  destruct (ranked_window_ok_sound A a_state succs Sl ranks w Hgate)
    as [Hranks Hbound].
  eapply closed_tail_window_bound; eauto.
Qed.

(** Supplied n-gram certificate. The anchor is simulated only to [t];
    neither this checker nor its soundness proof simulates to [B]. *)
Definition ngram_ranked_tail_ok (tm : TM) (n : nat) (lset rset : gset)
    (cc : cconf) (Sl : list cconf) (ranks : St -> cconf -> nat)
    (w : nat) : bool :=
  ng_seed_ok n lset rset cc &&
  mem cconf cconf_enc (ng_start n cc) Sl &&
  closed_b cconf cconf_enc (ng_succs tm lset rset) Sl &&
  ranked_window_ok ec_state (ng_succs tm lset rset) Sl ranks w.

Theorem ngram_ranked_tail_ok_sound : forall tm n lset rset cc Sl ranks
    t B w,
  1 <= n -> t <= B -> csteps tm t c0 = Some cc ->
  ngram_ranked_tail_ok tm n lset rset cc Sl ranks w = true ->
  WindowBound tm B w.
Proof.
  intros tm n lset rset cc Sl ranks t B w Hn Ht Hanchor Hgate.
  unfold ngram_ranked_tail_ok in Hgate.
  apply andb_true_iff in Hgate as [Hgate Hrank].
  apply andb_true_iff in Hgate as [Hgate Hcl].
  apply andb_true_iff in Hgate as [Hseed Hmem].
  eapply (ranked_window_ok_window_bound tm cconf cconf_enc ec_state
    (ng_succs tm lset rset) (ng_covers n lset rset)
    cconf_enc_inj).
  - intros a c Hcov. eapply ng_covers_state; eauto.
  - intros a c Hcov. apply ng_succs_sound; assumption.
  - exact Hcl.
  - apply (mem_In cconf cconf_enc cconf_enc_inj). exact Hmem.
  - apply ng_start_covers. exact Hseed.
  - rewrite <- lift_c0. apply csteps_lift. exact Hanchor.
  - exact Ht.
  - exact Hrank.
Qed.

(** The existing untrusted n-gram/closure/rank searches can produce a
    waiting certificate too, provided the new quantitative gate passes.
    [B] is a logical cutoff parameter of the soundness theorem only. *)
Definition ngram_ranked_search (tm : TM) (n t fuel rounds w : nat) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
    let '(_, (l, _, r)) := cc in
    let a0 := ng_start n cc in
    let '(lset, rset) := ng_grow tm a0 fuel rounds
      (gadds (ng_seed_side n l) gempty)
      (gadds (ng_seed_side n r) gempty) in
    match close cconf cconf_enc (ng_succs tm lset rset)
      fuel [] PositiveSet.empty [a0] with
    | Some Sl => ngram_ranked_tail_ok tm n lset rset cc Sl
        (compute_ranks cconf cconf_enc ec_state (ng_succs tm lset rset) Sl) w
    | None => false
    end
  | None => false
  end.

Theorem ngram_ranked_search_sound : forall tm n t fuel rounds w B,
  t <= B -> ngram_ranked_search tm n t fuel rounds w = true ->
  WindowBound tm B w.
Proof.
  intros tm n t fuel rounds w B Ht H.
  unfold ngram_ranked_search in H. apply andb_true_iff in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  cbv beta iota zeta in H.
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  match type of H with
  | (match ?G with Some _ => _ | None => _ end) = true =>
      destruct G as [Sl|] eqn:Ecl
  end; [|discriminate].
  eapply ngram_ranked_tail_ok_sound; eauto.
Qed.

(** Regression for the essential extra step: the edge gate accepts a
    zero-rank non-target whose successor is the target. *)
Example rank_zero_target_edge :
  edge_ok St (fun q => q) StB (fun _ => 0) StA StB = true.
Proof. reflexivity. Qed.

Module RankedRegression.
  (** Two alternating states on the blank tape need a one-step window.
      This checks the complete n-gram search-to-window proof path. *)
  Definition alternating : TM := fun q _ =>
    Some (mkTrans S0 DR (match q with StA => StB | _ => StA end)).

  Example alternating_one_checked :
    ngram_ranked_search alternating 1 0 16 4 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  Example alternating_zero_rejected :
    ngram_ranked_search alternating 1 0 16 4 0 = false.
  Proof. vm_compute. reflexivity. Qed.

  Theorem alternating_window : forall B, WindowBound alternating B 1.
  Proof.
    intro B. apply (ngram_ranked_search_sound alternating 1 0 16 4 1 B);
      [lia|exact alternating_one_checked].
  Qed.
End RankedRegression.
