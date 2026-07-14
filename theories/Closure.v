(** * Closure: the generic covering-abstraction / liveness engine.

    The shared skeleton of the BBB harness's whole n-gram / RepWL
    never-quasihalting family (docs/neverqh.md upstream):

    1. A *covering abstraction*: abstract nodes [A] with a semantic
       [covers : A -> ExecState -> Prop] and a computable successor
       function [succs : A -> option (list A)] ([None] = the node
       cannot exclude halting), such that a covered concrete step
       lands on a covered successor ([succs_sound]).

    2. A *closed set*: a list of nodes each of whose successors stays
       in the list ([closed_b]).  Containing a cover of the real
       configuration at step [t], it yields non-halting and "every
       later concrete configuration is covered"
       ([closure_invariant]).

    3. *Liveness by ranks*: state [q] recurs if some [rank : A -> nat]
       strictly decreases along every q-avoiding edge out of the
       closed set ([rank_ok]).  A q-avoiding stretch of the concrete
       run projects to a rank-decreasing abstract walk, so within
       [rank] steps the run must visit [q] ([rank_find]) -- no SCC or
       pigeonhole graph theory needed.  Rank existence is equivalent
       to the C verifier's per-state acyclicity check, and the
       upstream ranking rules (a)/(b) are refinements of exactly this
       argument.

    Nodes must be CANONICAL: [a_eqb] is boolean equality that implies
    term equality ([a_eqb_sound]), so instances normalize their
    representations (strip padding, sort sets, or encode to
    [positive]).  Everything search-like (the worklist [close], the
    Bellman-style [compute_ranks]) is UNTRUSTED: the checker re-checks
    closedness and rank decrease explicitly, and only those checks
    carry proofs.

    Silent states come out for free: the engine skips liveness for
    states visited neither in the simulated prefix nor anywhere in
    the closure -- such states are provably never visited, matching
    the upstream [neverqh_rwlsilent] convention (a never-visited
    state does not witness quasihalting). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

Section ClosureEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_eqb : A -> A -> bool.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).

  (** ** Computational layer *)

  Definition mem (a : A) (l : list A) : bool := existsb (a_eqb a) l.

  (** Worklist closure search.  Untrusted: the result is re-checked
      by [closed_b]. *)
  Fixpoint close (fuel : nat) (seen todo : list A) : option (list A) :=
    match fuel with
    | 0 => None
    | S f =>
        match todo with
        | [] => Some seen
        | a :: todo' =>
            if mem a seen then close f seen todo'
            else match succs a with
                 | None => None
                 | Some l => close f (a :: seen) (l ++ todo')
                 end
        end
    end.

  Definition node_ok (Sl : list A) (a : A) : bool :=
    match succs a with
    | Some l => forallb (fun a' => mem a' Sl) l
    | None => false
    end.

  Definition closed_b (Sl : list A) : bool := forallb (node_ok Sl) Sl.

  Definition edge_ok (q : St) (rnk : A -> nat) (a a' : A) : bool :=
    implb (negb (st_eqb (a_state a') q)) (rnk a' <? rnk a).

  Definition rank_ok (Sl : list A) (q : St) (rnk : A -> nat) : bool :=
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else match succs a with
           | Some l => forallb (edge_ok q rnk a) l
           | None => false
           end) Sl.

  (** Untrusted longest-path rank computation: Bellman-style
      iteration on the q-avoiding subgraph.  Converges within
      [length Sl] passes when that subgraph is acyclic; produces
      values [rank_ok] rejects otherwise (no valid rank exists on a
      cyclic subgraph, so garbage is harmless). *)

  Definition lookup_rank (r : list (A * nat)) (a : A) : nat :=
    match find (fun p => a_eqb a (fst p)) r with
    | Some p => snd p
    | None => 0
    end.

  Definition nonq_succs (q : St) (a : A) : list A :=
    match succs a with
    | Some l => filter (fun a' => negb (st_eqb (a_state a') q)) l
    | None => []
    end.

  Definition rank_pass (Sl : list A) (q : St) (r : list (A * nat))
    : list (A * nat) :=
    map (fun a =>
      (a, match nonq_succs q a with
          | [] => 0
          | l => S (fold_left Nat.max (map (lookup_rank r) l) 0)
          end)) Sl.

  Fixpoint rank_iter (k : nat) (Sl : list A) (q : St)
    (r : list (A * nat)) : list (A * nat) :=
    match k with
    | 0 => r
    | S k' => rank_iter k' Sl q (rank_pass Sl q r)
    end.

  Definition compute_ranks (Sl : list A) (q : St) : A -> nat :=
    lookup_rank (rank_iter (S (length Sl)) Sl q
                           (map (fun a => (a, 0)) Sl)).

  (** ** The checker *)

  Definition closure_check_neverqh (t fuel : nat) (a0 : A) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close fuel [] [a0] with
        | Some Sl =>
            closed_b Sl && mem a0 Sl &&
            forallb (fun q =>
              implb (cvisits tm c0 t q
                     || existsb (fun a => st_eqb (a_state a) q) Sl)
                    (rank_ok Sl q (compute_ranks Sl q))) all_St
        | None => false
        end
    | None => false
    end.

  (** ** Logical layer *)

  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_eqb_sound : forall x y, a_eqb x y = true -> x = y.
  Hypothesis covers_state : forall a c, covers a c -> a_state a = fst c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  Lemma mem_In : forall a Sl, mem a Sl = true -> In a Sl.
  Proof.
    intros a Sl Hm. unfold mem in Hm.
    apply existsb_exists in Hm.
    destruct Hm as (y & Hy & Heq).
    apply a_eqb_sound in Heq. subst. assumption.
  Qed.

  (** One covered concrete step inside a closed set. *)
  Lemma closed_step : forall Sl a c,
    closed_b Sl = true -> In a Sl -> covers a c ->
    exists c' l a', step tm c = Some c' /\ succs a = Some l /\
      In a' l /\ In a' Sl /\ covers a' c'.
  Proof.
    intros Sl a c Hcl HIn Hcov.
    assert (Hnode : node_ok Sl a = true).
    { unfold closed_b in Hcl. rewrite forallb_forall in Hcl. auto. }
    unfold node_ok in Hnode.
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    pose proof (succs_sound a c Hcov) as Hss. rewrite Es in Hss.
    destruct (step tm c) as [c'|] eqn:Est; [|contradiction].
    destruct Hss as (a' & HInl & Hcov').
    rewrite forallb_forall in Hnode.
    exists c', l, a'.
    repeat split; try assumption.
    apply mem_In. auto.
  Qed.

  Lemma closure_invariant : forall Sl,
    closed_b Sl = true ->
    forall a c, In a Sl -> covers a c ->
    forall k, exists c' a',
      stepn tm k c = Some c' /\ In a' Sl /\ covers a' c'.
  Proof.
    intros Sl Hcl a c HIn Hcov k.
    induction k.
    - exists c, a. split; [reflexivity | split; assumption].
    - destruct IHk as (c' & a' & Hst & HIn' & Hcov').
      destruct (closed_step Sl a' c' Hcl HIn' Hcov')
        as (c'' & l & a'' & Hstep & _ & _ & HIn'' & Hcov'').
      exists c'', a''.
      split; [| split; assumption].
      replace (S k) with (k + 1) by lia.
      rewrite stepn_add, Hst. cbn [stepn]. rewrite Hstep. reflexivity.
  Qed.

  (** From any covered configuration at run index [m], a visit to [q]
      happens within [rnk] further steps -- the rank-decreasing walk
      cannot avoid [q] forever. *)
  Lemma rank_find : forall Sl q rnk,
    closed_b Sl = true -> rank_ok Sl q rnk = true ->
    forall r a c m, rnk a < r -> In a Sl -> covers a c ->
    stepn tm m InitES = Some c ->
    exists n, m <= n /\ VisitsAt tm q n.
  Proof.
    intros Sl q rnk Hcl Hro.
    induction r; intros a c m Hr HIn Hcov Hm; [lia|].
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - (* the covered node itself is a q-visit *)
      apply st_eqb_spec in Eq.
      exists m. split; [lia|].
      exists c. split; [assumption|].
      rewrite <- (covers_state a c Hcov). assumption.
    - (* step once; either the successor visits q or rank drops *)
      destruct (closed_step Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      assert (Hm' : stepn tm (S m) InitES = Some c').
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists c'. split; [assumption|].
        rewrite <- (covers_state a' c' Hcov'). assumption.
      + (* the checked edge decreases the rank *)
        assert (Hlt : rnk a' < rnk a).
        { unfold rank_ok in Hro. rewrite forallb_forall in Hro.
          specialize (Hro a HIn). rewrite Eq, Es in Hro.
          rewrite forallb_forall in Hro.
          specialize (Hro a' HInl).
          unfold edge_ok in Hro. rewrite Eq' in Hro. simpl in Hro.
          apply Nat.ltb_lt. assumption. }
        destruct (IHr a' c' (S m)) as (n & Hn & Hv);
          try assumption; try lia.
        exists n. split; [lia | assumption].
  Qed.

  Theorem closure_check_neverqh_sound : forall t fuel a0,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    closure_check_neverqh t fuel a0 = true -> NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 Hstart H. unfold closure_check_neverqh in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close fuel [] [a0]) as [Sl|]; [|discriminate].
    apply andb_prop in H as [H Hq].
    apply andb_prop in H as [Hcl Hin].
    apply mem_In in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    (* the liveness premise for q holds, so rank_ok was checked *)
    assert (Hro : rank_ok Sl q (compute_ranks Sl q) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_St_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cvisits tm c0 t q
                      || existsb (fun a => st_eqb (a_state a) q) Sl = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - (* visited at or after t: some closure node has state q *)
          apply orb_true_intro; right.
          destruct (closure_invariant Sl Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply st_eqb_spec. rewrite (covers_state a' c' Hcov'). assumption.
        - (* visited strictly before t: caught by the prefix scan *)
          apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cvisits_complete; [exact Hlt | exact Hcn' | exact Hqn]. }
      rewrite Hprem in Hq. destruct (rank_ok Sl q (compute_ranks Sl q));
        [reflexivity | discriminate]. }
    (* fetch the covered configuration at index max N t and search *)
    set (M := Nat.max N t).
    destruct (closure_invariant Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (rank_find Sl q (compute_ranks Sl q) Hcl Hro
                (S (compute_ranks Sl q aM)) aM cM M)
      as (n & Hn & Hv); try assumption; try lia.
    exists n. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End ClosureEngine.
