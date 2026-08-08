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

    Nodes must be CANONICAL: [a_enc] is an injective [positive]
    encoding ([a_enc_inj]), so instances normalize their
    representations (strip padding) before encoding.  All set
    membership is Patricia-trie lookup on encodings ([PosEnc]): the
    checker re-builds the trie of the candidate list once ([pset_of])
    and [pset_of_mem] turns trie hits back into list membership, the
    only direction soundness needs.  Everything search-like (the
    worklist [close], the Bellman-style [compute_ranks]) is
    UNTRUSTED: the checker re-checks closedness and rank decrease
    explicitly, and only those checks carry proofs.

    Silent states come out for free: the engine skips liveness for
    states visited neither in the simulated prefix nor anywhere in
    the closure -- such states are provably never visited, matching
    the upstream [neverqh_rwlsilent] convention (a never-visited
    state does not witness quasihalting). *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

Section ClosureEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).

  (** ** Computational layer *)

  (** Trie of a candidate list's encodings; membership through it.
      [mem a Sl] rebuilds the trie, so it is for one-shot checks
      only -- the per-successor checks below take a prebuilt pool. *)
  Definition apool (Sl : list A) : PositiveSet.t := pset_of A a_enc Sl.

  Definition mem (a : A) (Sl : list A) : bool :=
    pset_mem A a_enc a (apool Sl).

  (** Worklist closure search.  Untrusted: the result is re-checked
      by [closed_b].  [sp] mirrors [seen] as a trie. *)
  Fixpoint close (fuel : nat) (seen : list A) (sp : PositiveSet.t)
      (todo : list A) : option (list A) :=
    match fuel with
    | 0 => None
    | S f =>
        match todo with
        | [] => Some seen
        | a :: todo' =>
            if pset_mem A a_enc a sp then close f seen sp todo'
            else match succs a with
                 | None => None
                 | Some l =>
                     close f (a :: seen) (pset_add A a_enc a sp) (l ++ todo')
                 end
        end
    end.

  Definition node_ok (sp : PositiveSet.t) (a : A) : bool :=
    match succs a with
    | Some l => forallb (fun a' => pset_mem A a_enc a' sp) l
    | None => false
    end.

  Definition closed_b (Sl : list A) : bool :=
    forallb (node_ok (apool Sl)) Sl.

  Definition edge_ok (q : St) (rnk : A -> nat) (a a' : A) : bool :=
    implb (negb (st_eqb (a_state a') q)) (rnk a' <? rnk a).

  Definition rank_ok (Sl : list A) (q : St) (rnk : A -> nat) : bool :=
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else match succs a with
           | Some l => forallb (edge_ok q rnk a) l
           | None => false
           end) Sl.

  (** Untrusted longest-path rank computation, by reverse-topological
      *peeling* of the q-avoiding subgraph: a pass assigns
      [1 + max (succ ranks)] to every remaining node all of whose
      q-avoiding successors are already ranked, so ranks strictly
      decrease along every assigned q-avoiding edge by construction.
      Acyclic subgraphs finish in depth-many passes; on a cyclic one
      a pass eventually assigns nothing and we stop immediately,
      leaving the cycle's nodes at the default rank 0, which
      [rank_ok] rejects (no valid rank exists there, so bailing out
      fast loses nothing).  Ranks live in a [PositiveMap] keyed by
      node encoding. *)

  Definition lookup_rank (r : PositiveMap.tree nat) (a : A) : nat :=
    pmap_get A a_enc r a.

  Definition nonq_succs (q : St) (a : A) : list A :=
    match succs a with
    | Some l => filter (fun a' => negb (st_eqb (a_state a') q)) l
    | None => []
    end.

  Definition ranked (r : PositiveMap.tree nat) (a : A) : bool :=
    match PositiveMap.find (a_enc a) r with
    | Some _ => true
    | None => false
    end.

  (** One pass: peel every ready node; collect the rest (reversed --
      order is irrelevant) and whether anything was peeled. *)
  Definition peel_pass (q : St) (st : PositiveMap.tree nat * list A * bool)
      (rem : list A) : PositiveMap.tree nat * list A * bool :=
    fold_left (fun '(r, stuck, prog) a =>
      let sl := nonq_succs q a in
      if forallb (ranked r) sl
      then (PositiveMap.add (a_enc a)
              (match sl with
               | [] => 0
               | _ => S (fold_left Nat.max (map (lookup_rank r) sl) 0)
               end) r, stuck, true)
      else (r, a :: stuck, prog)) rem st.

  Fixpoint peel_iter (k : nat) (q : St) (r : PositiveMap.tree nat)
      (rem : list A) : PositiveMap.tree nat :=
    match k, rem with
    | 0, _ | _, [] => r
    | S k', _ =>
        let '(r', stuck, prog) := peel_pass q (r, [], false) rem in
        if prog then peel_iter k' q r' stuck else r'
    end.

  Definition compute_ranks (Sl : list A) (q : St) : A -> nat :=
    lookup_rank
      (peel_iter (S (length Sl)) q (PositiveMap.empty nat)
         (filter (fun a => negb (st_eqb (a_state a) q)) Sl)).

  (** ** The checker *)

  Definition closure_check_neverqh (t fuel : nat) (a0 : A) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            forallb (fun q =>
              if (if cvisits tm c0 t q then true
                  else existsb (fun a => st_eqb (a_state a) q) Sl)
              then rank_ok Sl q (compute_ranks Sl q)
              else true) all_St
        | None => false
        end
    | None => false
    end.

  (** ** Logical layer *)

  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_state : forall a c, covers a c -> a_state a = fst c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  (** ** [close]'s worklist invariant, proved directly

      A successful exploration IS closed and contains its root, so
      the boolean re-verification pass ([closed_b] + [mem]) that the
      checkers used to execute at runtime is redundant: the checkers
      now rely on [close_root_spec] and skip recomputing every node's
      successors a second time and rebuilding the trie. *)

  Lemma pset_mem_add : forall x y s,
    pset_mem A a_enc x (pset_add A a_enc y s) = true <->
    x = y \/ pset_mem A a_enc x s = true.
  Proof.
    intros x y s. unfold pset_mem, pset_add.
    rewrite PositiveSet.mem_spec, PositiveSet.add_spec.
    rewrite <- PositiveSet.mem_spec.
    split.
    - intros [E | Hm]; [left; apply a_enc_inj; exact E | right; exact Hm].
    - intros [-> | Hm]; [left; reflexivity | right; exact Hm].
  Qed.

  Lemma pset_of_In : forall x l,
    In x l -> pset_mem A a_enc x (pset_of A a_enc l) = true.
  Proof.
    intros x l Hin. unfold pset_of.
    revert Hin.
    enough (H : forall s, In x l \/ PositiveSet.mem (a_enc x) s = true ->
      PositiveSet.mem (a_enc x)
        (fold_left (fun s a => pset_add A a_enc a s) l s) = true).
    { intro Hin. apply H. left; exact Hin. }
    induction l as [|h t IH]; simpl; intros s Hcase.
    - destruct Hcase as [[] | Hs]. exact Hs.
    - apply IH.
      destruct Hcase as [[-> | Hin] | Hs].
      + right. unfold pset_add.
        apply PositiveSet.mem_spec, PositiveSet.add_spec.
        left; reflexivity.
      + left; exact Hin.
      + right. unfold pset_add.
        apply PositiveSet.mem_spec, PositiveSet.add_spec.
        right. apply PositiveSet.mem_spec. exact Hs.
  Qed.

  Lemma close_spec_aux : forall fuel seen sp todo Sl,
    close fuel seen sp todo = Some Sl ->
    (forall x, pset_mem A a_enc x sp = true <-> In x seen) ->
    (forall x, In x seen -> exists l, succs x = Some l /\
       forall y, In y l -> pset_mem A a_enc y sp = true \/ In y todo) ->
    incl seen Sl /\
    (forall x, In x todo -> In x Sl) /\
    (forall x, In x Sl -> exists l, succs x = Some l /\
       forall y, In y l -> In y Sl).
  Proof.
    induction fuel as [|f IH]; intros seen sp todo Sl H I1 I2;
      simpl in H; [discriminate|].
    destruct todo as [|a todo'].
    - (* drained: seen is the closure *)
      injection H as <-.
      split; [intro x; exact (fun h => h)|].
      split; [intros x [] |].
      intros x Hx.
      destruct (I2 x Hx) as (l & Hs & Hl).
      exists l. split; [exact Hs|].
      intros y Hy.
      destruct (Hl y Hy) as [Hm | []].
      apply I1; exact Hm.
    - destruct (pset_mem A a_enc a sp) eqn:Ea.
      + (* already seen *)
        destruct (IH seen sp todo' Sl H I1) as (Ha & Hb & Hc).
        { intros x Hx.
          destruct (I2 x Hx) as (l & Hs & Hl).
          exists l. split; [exact Hs|].
          intros y Hy.
          destruct (Hl y Hy) as [Hm | [-> | Ht]];
            [left; exact Hm | left; exact Ea | right; exact Ht]. }
        split; [exact Ha|].
        split; [|exact Hc].
        intros x [-> | Hx]; [apply Ha, I1; exact Ea | exact (Hb x Hx)].
      + (* new node *)
        destruct (succs a) as [l|] eqn:Es; [|discriminate].
        destruct (IH (a :: seen) (pset_add A a_enc a sp) (l ++ todo') Sl H)
          as (Ha & Hb & Hc).
        { intros x. rewrite pset_mem_add. rewrite I1.
          simpl.
          split; (intros [E | Hin]; [left; congruence | right; assumption]). }
        { intros x [<- | Hx].
          - exists l. split; [exact Es|].
            intros y Hy. right. apply in_or_app. left; exact Hy.
          - destruct (I2 x Hx) as (lx & Hsx & Hlx).
            exists lx. split; [exact Hsx|].
            intros y Hy.
            destruct (Hlx y Hy) as [Hm | [-> | Ht]].
            + left. apply pset_mem_add. right; exact Hm.
            + left. apply pset_mem_add. left; reflexivity.
            + right. apply in_or_app. right; exact Ht. }
        split.
        { intros x Hx. apply Ha. right; exact Hx. }
        split; [|exact Hc].
        intros x [-> | Hx].
        * apply Ha. left; reflexivity.
        * apply Hb. apply in_or_app. right; exact Hx.
  Qed.

  Lemma close_root_spec : forall fuel a0 Sl,
    close fuel [] PositiveSet.empty [a0] = Some Sl ->
    mem a0 Sl = true /\ closed_b Sl = true.
  Proof.
    intros fuel a0 Sl H.
    destruct (close_spec_aux fuel [] PositiveSet.empty [a0] Sl H)
      as (_ & Hroot & Hclosed).
    { intros x. unfold pset_mem.
      split; [|intros []].
      intro Hm. apply PositiveSet.mem_spec in Hm.
      now apply PositiveSet.empty_spec in Hm. }
    { intros x []. }
    split.
    - unfold mem, apool. apply pset_of_In. apply Hroot. left; reflexivity.
    - unfold closed_b. apply forallb_forall.
      intros x Hx.
      destruct (Hclosed x Hx) as (l & Hs & Hl).
      unfold node_ok. rewrite Hs.
      apply forallb_forall.
      intros y Hy. unfold apool. apply pset_of_In. exact (Hl y Hy).
  Qed.

  Lemma mem_In : forall a Sl, mem a Sl = true -> In a Sl.
  Proof.
    intros a Sl Hm.
    exact (pset_of_mem A a_enc a_enc_inj a Sl Hm).
  Qed.

  (** One covered concrete step inside a closed set. *)
  Lemma closed_step : forall Sl a c,
    closed_b Sl = true -> In a Sl -> covers a c ->
    exists c' l a', step tm c = Some c' /\ succs a = Some l /\
      In a' l /\ In a' Sl /\ covers a' c'.
  Proof.
    intros Sl a c Hcl HIn Hcov.
    assert (Hnode : node_ok (apool Sl) a = true).
    { unfold closed_b in Hcl. rewrite forallb_forall in Hcl. auto. }
    unfold node_ok in Hnode.
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    pose proof (succs_sound a c Hcov) as Hss. rewrite Es in Hss.
    destruct (step tm c) as [c'|] eqn:Est; [|contradiction].
    destruct Hss as (a' & HInl & Hcov').
    rewrite forallb_forall in Hnode.
    exists c', l, a'.
    repeat split; try assumption.
    apply mem_In. unfold mem. auto.
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

  (** *** Reachability of [q] from a covered configuration

      Like [rank_find] but blank-tape-free: from ANY covered [c] the
      run reaches state [q] within [rnk a] steps.  This is the local
      liveness fact the wrapped-closure QHBound tier needs -- its run
      starts at the simulated configuration, not [InitES]. *)
  Lemma rank_reach : forall Sl q rnk,
    closed_b Sl = true -> rank_ok Sl q rnk = true ->
    forall r a c, rnk a < r -> In a Sl -> covers a c ->
    exists j c', stepn tm j c = Some c' /\ fst c' = q.
  Proof.
    intros Sl q rnk Hcl Hro.
    induction r as [|r IH]; intros a c Hr HIn Hcov; [lia|].
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - apply st_eqb_spec in Eq.
      exists 0, c. split; [reflexivity|].
      rewrite <- (covers_state a c Hcov). exact Eq.
    - destruct (closed_step Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists 1, c'. split.
        * cbn [stepn]. rewrite Hstep. reflexivity.
        * rewrite <- (covers_state a' c' Hcov'). exact Eq'.
      + assert (Hlt : rnk a' < rnk a).
        { unfold rank_ok in Hro. rewrite forallb_forall in Hro.
          specialize (Hro a HIn). rewrite Eq, Es in Hro.
          rewrite forallb_forall in Hro. specialize (Hro a' HInl).
          unfold edge_ok in Hro. rewrite Eq' in Hro. simpl in Hro.
          apply Nat.ltb_lt. exact Hro. }
        destruct (IH a' c' ltac:(lia) HIn' Hcov') as (j & c'' & Hsteps & Hq).
        exists (S j), c''. split; [| exact Hq].
        cbn [stepn]. rewrite Hstep. exact Hsteps.
  Qed.

  (** *** The QHBound liveness gate

      Every state that APPEARS as some closure node's state carries a
      rank certificate.  On a covered run each appearing state then
      recurs (so it is never quiet), while non-appearing states are
      never visited -- the split the wrapped-closure QHBound tier needs
      to bound every quiet state's last visit. *)
  Definition appears (Sl : list A) (q' : St) : bool :=
    existsb (fun a => st_eqb (a_state a) q') Sl.

  Definition live_ok (Sl : list A) : bool :=
    forallb (fun q' =>
      if appears Sl q' then rank_ok Sl q' (compute_ranks Sl q')
      else true) all_St.

  (** From a covered start, any visited state appears in the closure. *)
  Lemma live_visited_appears : forall Sl a0 c0',
    closed_b Sl = true -> In a0 Sl -> covers a0 c0' ->
    forall k c', stepn tm k c0' = Some c' -> appears Sl (fst c') = true.
  Proof.
    intros Sl a0 c0' Hcl HIn Hcov k c' Hk.
    destruct (closure_invariant Sl Hcl a0 c0' HIn Hcov k)
      as (c'' & a'' & Hst & HIn'' & Hcov'').
    rewrite Hk in Hst. injection Hst as <-.
    unfold appears. apply existsb_exists. exists a''.
    split; [exact HIn'' |].
    apply st_eqb_spec. apply (covers_state a'' c' Hcov'').
  Qed.

  (** An appearing state recurs: visited at arbitrarily large indices. *)
  Lemma live_appears_recur : forall Sl a0 c0' q',
    closed_b Sl = true -> live_ok Sl = true ->
    In a0 Sl -> covers a0 c0' ->
    appears Sl q' = true ->
    forall N, exists k c', N <= k /\ stepn tm k c0' = Some c' /\ fst c' = q'.
  Proof.
    intros Sl a0 c0' q' Hcl Hlive HIn Hcov Happ N.
    assert (Hro : rank_ok Sl q' (compute_ranks Sl q') = true).
    { unfold live_ok in Hlive. rewrite forallb_forall in Hlive.
      specialize (Hlive q' (all_St_complete q')).
      rewrite Happ in Hlive. exact Hlive. }
    destruct (closure_invariant Sl Hcl a0 c0' HIn Hcov N)
      as (cN & aN & HstN & HInN & HcovN).
    destruct (rank_reach Sl q' (compute_ranks Sl q') Hcl Hro
                (S (compute_ranks Sl q' aN)) aN cN
                (Nat.lt_succ_diag_r _) HInN HcovN)
      as (j & c' & Hj & Hq).
    exists (N + j), c'. split; [lia|]. split; [| exact Hq].
    rewrite stepn_add, HstN. exact Hj.
  Qed.

  Theorem closure_check_neverqh_sound : forall t fuel a0,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    closure_check_neverqh t fuel a0 = true -> NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 Hstart H. unfold closure_check_neverqh in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close fuel [] PositiveSet.empty [a0]) as [Sl|] eqn:Hcls;
      [|discriminate].
    rename H into Hq.
    destruct (close_root_spec fuel a0 Sl Hcls) as [Hin Hcl].
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
      (* stated in the nested-[if] form the checker now uses; it is
         definitionally [orb], so [orb_true_intro] still applies *)
      assert (Hprem : (if cvisits tm c0 t q then true
                       else existsb (fun a => st_eqb (a_state a) q) Sl)
                      = true).
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


  (** ** Lexicographic liveness: the ranking rules (a)/(b)

      The upstream rank procedure (docs/neverqh.md "Ranking
      liveness") deletes strictly-decreasing edges of nonincreasing
      measures (rule a) and SCCs whose every cycle strictly
      decreases a measure (rule b, via Bellman-Ford).  Its runs
      compile to LEXICOGRAPHIC certificates: an ordered list of
      components, each either a node rank or a measure with a scale
      [K], node potentials [phi] (the Bellman-Ford certificate) and
      an SCC gate; every q-avoiding edge must strictly decrease some
      component while non-increasing all earlier ones.  The tracked
      value of a measure component on the concrete (computable) run
      is [K * measure + phi] when gated, [0] outside the gate -- a
      natural number, so an infinite q-avoiding run would give an
      infinite lexicographically decreasing sequence of nat tuples:
      impossible.  Checking is per-edge and local; no SCC or graph
      theory enters the proofs. *)

  Inductive lexcomp : Type :=
  | LexRank (phi : A -> nat)
  | LexMeas (mval : cconf -> nat) (mdelta : A -> A -> Z)
            (K : nat) (phi : A -> nat) (gate : A -> bool).

  Definition comp_eval (comp : lexcomp) (a : A) (cc : cconf) : nat :=
    match comp with
    | LexRank phi => phi a
    | LexMeas mval _ K phi gate =>
        if gate a then K * mval cc + phi a else 0
    end.

  Definition comp_strict (comp : lexcomp) (a a' : A) : bool :=
    match comp with
    | LexRank phi => phi a' <? phi a
    | LexMeas _ md K phi gate =>
        gate a && gate a' &&
        (Z.of_nat K * md a a' + Z.of_nat (phi a') - Z.of_nat (phi a)
           <=? -1)%Z
    end.

  Definition comp_noninc (comp : lexcomp) (a a' : A) : bool :=
    match comp with
    | LexRank phi => phi a' <=? phi a
    | LexMeas _ md K phi gate =>
        negb (gate a')
        || (gate a && gate a' &&
            (Z.of_nat K * md a a' + Z.of_nat (phi a') - Z.of_nat (phi a)
               <=? 0)%Z)
    end.

  Fixpoint lex_edge_ok (comps : list lexcomp) (a a' : A) : bool :=
    match comps with
    | [] => false
    | comp :: rest =>
        if comp_strict comp a a' then true
        else if comp_noninc comp a a' then lex_edge_ok rest a a'
             else false
    end.

  Definition lex_ok (Sl : list A) (q : St) (comps : list lexcomp) : bool :=
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else match succs a with
           | Some l => forallb (fun a' =>
                         if st_eqb (a_state a') q then true
                         else lex_edge_ok comps a a') l
           | None => false
           end) Sl.

  Definition lex_tuple (comps : list lexcomp) (a : A) (cc : cconf)
    : list nat := map (fun comp => comp_eval comp a cc) comps.

  Definition closure_check_neverqh_lex (t fuel : nat) (a0 : A)
      (cert : St -> list lexcomp) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            forallb (fun q =>
              if (if cvisits tm c0 t q then true
                  else existsb (fun a => st_eqb (a_state a) q) Sl)
              then lex_ok Sl q (cert q)
              else true) all_St
        | None => false
        end
    | None => false
    end.

  (** *** Well-foundedness of the lexicographic order *)

  Fixpoint lexlt (xs ys : list nat) : Prop :=
    match xs, ys with
    | x :: xs', y :: ys' =>
        (x < y /\ length xs' = length ys') \/ (x = y /\ lexlt xs' ys')
    | _, _ => False
    end.

  Lemma lexlt_length : forall xs ys, lexlt xs ys -> length xs = length ys.
  Proof.
    induction xs as [|x xs' IH]; intros [|y ys'] H; simpl in *;
      try contradiction.
    destruct H as [[_ Hl] | [_ Hl]]; [lia | rewrite (IH _ Hl); lia].
  Qed.

  Lemma lexlt_wf_len : forall k xs, length xs = k -> Acc lexlt xs.
  Proof.
    induction k as [|k IHk]; intros xs Hk.
    - destruct xs; [|discriminate].
      constructor. intros ys Hys. destruct ys; simpl in Hys; contradiction.
    - destruct xs as [|x t]; [discriminate|].
      injection Hk as Hk.
      revert t Hk.
      induction x as [x IHx] using lt_wf_ind.
      intros t Hk.
      pose proof (IHk t Hk) as Hacc.
      revert Hk.
      induction Hacc as [t Hacc IHt].
      intros Hk.
      constructor. intros ys Hys.
      destruct ys as [|y t']; simpl in Hys; [contradiction|].
      destruct Hys as [[Hlt Hlen] | [-> Hl]].
      + apply (IHx y Hlt t'). congruence.
      + apply IHt; [exact Hl|].
        rewrite (lexlt_length _ _ Hl). exact Hk.
  Qed.

  (** *** Soundness of the lexicographic liveness check *)

  Definition comp_exact (comp : lexcomp) : Prop :=
    match comp with
    | LexRank _ => True
    | LexMeas mval md _ _ _ =>
        forall a cc a' cc' l,
          covers a (lift cc) -> covers a' (lift cc') ->
          cstep tm cc = Some cc' ->
          succs a = Some l -> In a' l ->
          Z.of_nat (mval cc') = (Z.of_nat (mval cc) + md a a')%Z
    end.

  Lemma lex_edge_decrease : forall comps a cc a' cc' l,
    Forall comp_exact comps ->
    covers a (lift cc) -> covers a' (lift cc') ->
    cstep tm cc = Some cc' ->
    succs a = Some l -> In a' l ->
    lex_edge_ok comps a a' = true ->
    lexlt (lex_tuple comps a' cc') (lex_tuple comps a cc).
  Proof.
    induction comps as [|comp rest IH];
      intros a cc a' cc' l Hex Hca Hca' Hstep Es HInl He; simpl in He;
      [discriminate|].
    inversion Hex as [|? ? Hex1 Hexr]; subst.
    assert (Hlen : length (lex_tuple rest a' cc')
                   = length (lex_tuple rest a cc)).
    { unfold lex_tuple. rewrite !map_length. reflexivity. }
    apply orb_prop in He as [Hs | He].
    - (* head strictly decreases *)
      left. split; [|exact Hlen].
      destruct comp as [phi | mval md K phi gate]; simpl in Hs |- *.
      + apply Nat.ltb_lt in Hs. exact Hs.
      + apply andb_prop in Hs as [Hg Hz].
        apply andb_prop in Hg as [Hga Hga'].
        rewrite Hga, Hga'.
        apply Z.leb_le in Hz.
        pose proof (Hex1 a cc a' cc' l Hca Hca' Hstep Es HInl) as Hd.
        lia.
    - apply andb_prop in He as [Hni He].
      assert (Hle : comp_eval comp a' cc' <= comp_eval comp a cc).
      { destruct comp as [phi | mval md K phi gate]; simpl in Hni |- *.
        - apply Nat.leb_le in Hni. exact Hni.
        - apply orb_prop in Hni as [Hng | Hni].
          + rewrite negb_true_iff in Hng. rewrite Hng. lia.
          + apply andb_prop in Hni as [Hg Hz].
            apply andb_prop in Hg as [Hga Hga'].
            rewrite Hga, Hga'.
            apply Z.leb_le in Hz.
            pose proof (Hex1 a cc a' cc' l Hca Hca' Hstep Es HInl) as Hd.
            lia. }
      destruct (Nat.lt_ge_cases (comp_eval comp a' cc')
                                (comp_eval comp a cc)) as [Hlt | Hge].
      + left. split; [exact Hlt | exact Hlen].
      + right. split; [lia|].
        eapply IH; eauto.
  Qed.

  Lemma lex_find : forall Sl q comps,
    closed_b Sl = true ->
    lex_ok Sl q comps = true ->
    Forall comp_exact comps ->
    forall tuple, Acc lexlt tuple ->
    forall a cc m,
    tuple = lex_tuple comps a cc ->
    In a Sl -> covers a (lift cc) ->
    stepn tm m InitES = Some (lift cc) ->
    exists n', m <= n' /\ VisitsAt tm q n'.
  Proof.
    intros Sl q comps Hcl Hok Hex tuple Hacc.
    induction Hacc as [tuple Hacc IH].
    intros a cc m -> HIn Hcov Hm.
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - apply st_eqb_spec in Eq.
      exists m. split; [lia|].
      exists (lift cc). split; [assumption|].
      rewrite <- (covers_state a (lift cc) Hcov). assumption.
    - destruct (closed_step Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      assert (Hm' : stepn tm (S m) InitES = Some (lift cc')).
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists (lift cc'). split; [assumption|].
        rewrite <- (covers_state a' _ Hcov'). assumption.
      + assert (He : lex_edge_ok comps a a' = true).
        { unfold lex_ok in Hok. rewrite forallb_forall in Hok.
          specialize (Hok a HIn). rewrite Eq, Es in Hok.
          rewrite forallb_forall in Hok.
          specialize (Hok a' HInl). rewrite Eq' in Hok.
          simpl in Hok. assumption. }
      destruct (IH (lex_tuple comps a' cc')
                  (lex_edge_decrease comps a cc a' cc' l Hex Hcov Hcov'
                     Hcc' Es HInl He)
                  a' cc' (S m) eq_refl HIn' Hcov' Hm')
        as (n' & Hn' & Hv).
      exists n'. split; [lia | assumption].
  Qed.

  (** *** Reachability variant of [lex_find] (blank-tape-free)

      Like [rank_reach]: from ANY covered computable configuration the
      run reaches state [q] -- the lexicographic tuple decreases on
      every q-avoiding step.  For the wrapped-closure QHBound tier,
      whose run starts at the simulated configuration. *)
  Lemma lex_reach : forall Sl q comps,
    closed_b Sl = true ->
    lex_ok Sl q comps = true ->
    Forall comp_exact comps ->
    forall tuple, Acc lexlt tuple ->
    forall a cc,
    tuple = lex_tuple comps a cc ->
    In a Sl -> covers a (lift cc) ->
    exists j c', stepn tm j (lift cc) = Some c' /\ fst c' = q.
  Proof.
    intros Sl q comps Hcl Hok Hex tuple Hacc.
    induction Hacc as [tuple Hacc IH].
    intros a cc -> HIn Hcov.
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - apply st_eqb_spec in Eq.
      exists 0, (lift cc). split; [reflexivity|].
      rewrite <- (covers_state a (lift cc) Hcov). exact Eq.
    - destruct (closed_step Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists 1, (lift cc'). split.
        * cbn [stepn]. rewrite Hstep. reflexivity.
        * rewrite <- (covers_state a' _ Hcov'). exact Eq'.
      + assert (He : lex_edge_ok comps a a' = true).
        { unfold lex_ok in Hok. rewrite forallb_forall in Hok.
          specialize (Hok a HIn). rewrite Eq, Es in Hok.
          rewrite forallb_forall in Hok.
          specialize (Hok a' HInl). rewrite Eq' in Hok.
          simpl in Hok. exact Hok. }
        destruct (IH (lex_tuple comps a' cc')
                    (lex_edge_decrease comps a cc a' cc' l Hex Hcov Hcov'
                       Hcc' Es HInl He)
                    a' cc' eq_refl HIn' Hcov')
          as (j & c'' & Hj & Hq).
        exists (S j), c''. split; [| exact Hq].
        cbn [stepn]. rewrite Hstep. exact Hj.
  Qed.

  (** *** Lex-gated QHBound liveness

      [live_lex_ok] generalizes [live_ok]: each appearing state is
      discharged by the plain acyclicity rank OR a lexicographic
      certificate (the full measure vocabulary).  The walk lemma
      [closure_invariant_c] tracks computable configurations so
      [lex_reach]'s [comp_exact] premises apply. *)

  Definition live_lex_ok (Sl : list A) (cert : St -> list lexcomp) : bool :=
    forallb (fun q' =>
      if appears Sl q'
      then (if rank_ok Sl q' (compute_ranks Sl q') then true
            else lex_ok Sl q' (cert q'))
      else true) all_St.

  Lemma closure_invariant_c : forall Sl,
    closed_b Sl = true ->
    forall a cc, In a Sl -> covers a (lift cc) ->
    forall k, exists cc' a',
      csteps tm k cc = Some cc' /\ In a' Sl /\ covers a' (lift cc').
  Proof.
    intros Sl Hcl a cc HIn Hcov k.
    induction k.
    - exists cc, a. repeat split; assumption.
    - destruct IHk as (cc' & a' & Hst & HIn' & Hcov').
      destruct (closed_step Sl a' (lift cc') Hcl HIn' Hcov')
        as (c'' & l & a'' & Hstep & _ & _ & HIn'' & Hcov'').
      destruct (cstep_lift_rev tm cc' c'' Hstep) as (cc'' & Hcc'' & Hlift).
      subst c''.
      exists cc'', a''. split; [| split; assumption].
      replace (S k) with (k + 1) by lia.
      rewrite csteps_add, Hst. cbn [csteps]. rewrite Hcc''. reflexivity.
  Qed.

  Lemma live_appears_recur_lex : forall Sl cert a0 cc0 q',
    closed_b Sl = true ->
    Forall comp_exact (cert q') ->
    live_lex_ok Sl cert = true ->
    In a0 Sl -> covers a0 (lift cc0) ->
    appears Sl q' = true ->
    forall N, exists k c',
      N <= k /\ stepn tm k (lift cc0) = Some c' /\ fst c' = q'.
  Proof.
    intros Sl cert a0 cc0 q' Hcl Hex Hlive HIn Hcov Happ N.
    destruct (closure_invariant_c Sl Hcl a0 cc0 HIn Hcov N)
      as (ccN & aN & HstN & HInN & HcovN).
    assert (HstN' : stepn tm N (lift cc0) = Some (lift ccN))
      by (apply csteps_lift; exact HstN).
    unfold live_lex_ok in Hlive. rewrite forallb_forall in Hlive.
    specialize (Hlive q' (all_St_complete q')). rewrite Happ in Hlive.
    simpl in Hlive. apply orb_true_iff in Hlive as [Hro | Hlex].
    - destruct (rank_reach Sl q' (compute_ranks Sl q') Hcl Hro
                  (S (compute_ranks Sl q' aN)) aN (lift ccN)
                  (Nat.lt_succ_diag_r _) HInN HcovN)
        as (j & c' & Hj & Hq).
      exists (N + j), c'. split; [lia|]. split; [| exact Hq].
      rewrite stepn_add, HstN'. exact Hj.
    - destruct (lex_reach Sl q' (cert q') Hcl Hlex Hex
                  (lex_tuple (cert q') aN ccN)
                  (lexlt_wf_len (length (lex_tuple (cert q') aN ccN)) _
                     eq_refl)
                  aN ccN eq_refl HInN HcovN)
        as (j & c' & Hj & Hq).
      exists (N + j), c'. split; [lia|]. split; [| exact Hq].
      rewrite stepn_add, HstN'. exact Hj.
  Qed.

  Theorem closure_check_neverqh_lex_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall comp_exact (cert q)) ->
    closure_check_neverqh_lex t fuel a0 cert = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqh_lex in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close fuel [] PositiveSet.empty [a0]) as [Sl|] eqn:Hcls;
      [|discriminate].
    rename H into Hq.
    destruct (close_root_spec fuel a0 Sl Hcls) as [Hin Hcl].
    apply mem_In in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    assert (Hro : lex_ok Sl q (cert q) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_St_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      (* stated in the nested-[if] form the checker now uses; it is
         definitionally [orb], so [orb_true_intro] still applies *)
      assert (Hprem : (if cvisits tm c0 t q then true
                       else existsb (fun a => st_eqb (a_state a) q) Sl)
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant Sl Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply st_eqb_spec. rewrite (covers_state a' c' Hcov'). assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cvisits_complete; [exact Hlt | exact Hcn' | exact Hqn]. }
      rewrite Hprem in Hq.
      destruct (lex_ok Sl q (cert q)); [reflexivity | discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (lex_find Sl q (cert q) Hcl Hro (Hcert q)
                (lex_tuple (cert q) aM ccM)
                (lexlt_wf_len (length (lex_tuple (cert q) aM ccM)) _ eq_refl)
                aM ccM M eq_refl HInM HcovM HM)
      as (n' & Hn' & Hv).
    exists n'. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

  (** ** Runner liveness: the fuel rule (c2)

      What the rank / lex measures leave undecided is dominated by
      *runner* SCCs (neverqh.md "Fuel-refined rank"): every alive
      intra-SCC edge moves the head the same way and every context
      holds fuel on that side.  Such an SCC cannot carry the
      infinitely-often set of a run: confined to it the head is
      monotone, so it crosses every cell ahead and the sided nonblank
      count drains to 0 -- contradicting "fuel >= 1 everywhere".

      This is a genuinely different liveness mechanism from a rank
      (no measure decreases per step over blank tape), and it stands
      on [Records]: the head-relative model's right window is a nat
      bounded by the step index ([extent_le_steps]) that a rightward
      step strictly shrinks ([step_right_shrinks]), while "fuel >= 1"
      keeps it positive -- an impossible infinite descent.

      The two node-level facts the abstraction must supply are taken
      as parameters here (the fuel-refined n-gram instance provides
      them: the head symbol pins the transition direction, and the
      tracked capped right-count >= 1 witnesses a right nonblank).
      Left-runners are handled by the [Mirror] machine transfer, so
      only the right case is proved. *)

  Variable node_moves_right : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.
  Hypothesis node_moves_right_sound : forall a c,
    node_moves_right a = true -> covers a c -> steps_right tm c.
  Hypothesis node_rfuel_ge1_sound : forall a c,
    node_rfuel_ge1 a = true -> covers a c -> has_right_nonblank (snd c).

  (** Every q-avoiding closure node moves right and holds right fuel. *)
  Definition runner_ok (Sl : list A) (q : St) : bool :=
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else node_moves_right a && node_rfuel_ge1 a) Sl.

  (** The record-argument descent: from a covered config whose right
      window is [R], a run that keeps avoiding [q] visits [q] within
      [R] steps -- each avoided step is a right move that shrinks the
      window, and fuel keeps it positive, so it cannot avoid [q]
      longer than the window is wide. *)
  Lemma runner_find_aux : forall Sl q,
    closed_b Sl = true -> runner_ok Sl q = true ->
    forall r a c m R, right_bounded (snd c) R -> R < r ->
    In a Sl -> covers a c ->
    stepn tm m InitES = Some c ->
    exists n, m <= n /\ VisitsAt tm q n.
  Proof.
    intros Sl q Hcl Hok.
    induction r as [|r IH]; intros a c m R HR Hr HIn Hcov Hm; [lia|].
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - (* the covered node itself is a q-visit *)
      apply st_eqb_spec in Eq.
      exists m. split; [lia|].
      exists c. split; [assumption|].
      rewrite <- (covers_state a c Hcov). assumption.
    - (* q avoided here: runner_ok forces the two node checks *)
      assert (Hmr : node_moves_right a && node_rfuel_ge1 a = true).
      { unfold runner_ok in Hok. rewrite forallb_forall in Hok.
        specialize (Hok a HIn). rewrite Eq in Hok. exact Hok. }
      apply andb_prop in Hmr as [Hmv Hfu].
      assert (Hnb : has_right_nonblank (snd c))
        by (apply (node_rfuel_ge1_sound a c Hfu Hcov)).
      assert (HR1 : 1 <= R) by (apply (has_right_nonblank_window_pos _ _ HR Hnb)).
      assert (Hsr : steps_right tm c)
        by (apply (node_moves_right_sound a c Hmv Hcov)).
      destruct (closed_step Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct c as [qc tpc]. destruct c' as [qc' tpc'].
      unfold steps_right in Hsr. simpl in Hsr.
      assert (HR' : right_bounded tpc' (Nat.pred R)).
      { apply (step_right_shrinks tm qc tpc qc' tpc' R Hstep Hsr HR). }
      assert (Hm' : stepn tm (S m) InitES = Some (qc', tpc')).
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (IH a' (qc', tpc') (S m) (Nat.pred R) HR')
        as (n & Hn & Hv); [lia | assumption .. |].
      exists n. split; [lia | assumption].
  Qed.

  Lemma runner_find : forall Sl q,
    closed_b Sl = true -> runner_ok Sl q = true ->
    forall a c m, In a Sl -> covers a c ->
    stepn tm m InitES = Some c ->
    exists n, m <= n /\ VisitsAt tm q n.
  Proof.
    intros Sl q Hcl Hok a c m HIn Hcov Hm.
    destruct (extent_le_steps tm m c Hm) as [HR _].
    apply (runner_find_aux Sl q Hcl Hok (S m) a c m m HR
             (Nat.lt_succ_diag_r m) HIn Hcov Hm).
  Qed.

  (** ** The combined fuel checker

      Each visited state is discharged by EITHER a lex-rank
      certificate (rules (a)/(b)) OR the runner rule (c2) -- exactly
      the mix the upstream [neverqh_fuel] procedure produces (rank
      measures peel most states; the surviving runner SCCs fall to
      (c2)).  The closure itself is unchanged; only the per-state
      liveness gate gains the runner alternative. *)

  Definition state_live_ok (Sl : list A) (cert : St -> list lexcomp)
      (q : St) : bool :=
    if lex_ok Sl q (cert q) then true else runner_ok Sl q.

  Definition closure_check_neverqh_fuel (t fuel : nat) (a0 : A)
      (cert : St -> list lexcomp) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            forallb (fun q =>
              if (if cvisits tm c0 t q then true
                  else existsb (fun a => st_eqb (a_state a) q) Sl)
              then state_live_ok Sl cert q
              else true) all_St
        | None => false
        end
    | None => false
    end.

  Theorem closure_check_neverqh_fuel_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall comp_exact (cert q)) ->
    closure_check_neverqh_fuel t fuel a0 cert = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqh_fuel in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close fuel [] PositiveSet.empty [a0]) as [Sl|] eqn:Hcls;
      [|discriminate].
    rename H into Hq.
    destruct (close_root_spec fuel a0 Sl Hcls) as [Hin Hcl].
    apply mem_In in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    assert (Hlive : state_live_ok Sl cert q = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_St_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      (* stated in the nested-[if] form the checker now uses; it is
         definitionally [orb], so [orb_true_intro] still applies *)
      assert (Hprem : (if cvisits tm c0 t q then true
                       else existsb (fun a => st_eqb (a_state a) q) Sl)
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant Sl Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply st_eqb_spec. rewrite (covers_state a' c' Hcov'). assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cvisits_complete; [exact Hlt | exact Hcn' | exact Hqn]. }
      rewrite Hprem in Hq.
      destruct (state_live_ok Sl cert q); [reflexivity | discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    assert (HNM : N <= M) by (unfold M; lia).
    unfold state_live_ok in Hlive. apply orb_true_iff in Hlive as [Hlex | Hrun].
    - (* discharged by the lex-rank certificate *)
      destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
      rewrite <- HliftM in HcovM, HM.
      destruct (lex_find Sl q (cert q) Hcl Hlex (Hcert q)
                  (lex_tuple (cert q) aM ccM)
                  (lexlt_wf_len (length (lex_tuple (cert q) aM ccM)) _ eq_refl)
                  aM ccM M eq_refl HInM HcovM HM)
        as (n' & Hn' & Hv).
      exists n'. split; [lia | assumption].
    - (* discharged by the runner rule (c2) *)
      destruct (runner_find Sl q Hcl Hrun aM cM M HInM HcovM HM)
        as (n' & Hn' & Hv).
      exists n'. split; [lia | assumption].
  Qed.

End ClosureEngine.
