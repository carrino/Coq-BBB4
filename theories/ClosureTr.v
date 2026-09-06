(** * ClosureTr: the covering-abstraction / liveness engine at
    TRANSITION level.

    The instruction-target port of Closure.v's plain-rank half
    (SCOPING_INSTR.md sections 3.3, 5): the same worklist closure, the
    same closed-set invariant, the same rank-descent liveness — with
    the target alphabet changed from the 4 states to the 8
    instructions.  An abstraction whose nodes pin the head symbol
    (every instance in this tree does: n-gram windows, history nodes,
    RepWL blocks all carry it) exposes [a_instr : A -> Instr] instead
    of [a_state : A -> St], and the engine concludes
    [NeverQuasiHaltsTr]: every FIRED instruction recurs.

    The state-level engine (Closure.v) is untouched; this file is a
    parallel section, not a refactor, so the finished BBB(4) proof
    cannot wobble.  The lex/fuel/runner gates port later by the same
    pattern; this file carries exactly what the phase-3 in-walk tiers
    and the instruction-wrap QHBound tier need:

    - [closure_check_neverqhtr] + soundness: the in-walk never tier;
    - [appears_tr] / [live_ok_tr] / [rank_reach_tr] /
      [live_appears_recur_tr]: the liveness gate the wrapped-closure
      QHBoundTr tier consumes. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records
  Closure.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Engine AnchorVisits AnchorVisitsTr.
Import ListNotations.
Open Scope nat_scope.

(** prefix scan: does instruction [tg] fire among the configurations
    [0 .. len-1] from [c]?  ([cvisits]'s shape, at instruction
    granularity.) *)
Fixpoint cfires (tm : TM) (c : cconf) (len : nat) (tg : Instr) : bool :=
  match len with
  | 0 => false
  | S m => instr_eqb (cinstr c) tg
           || match cstep tm c with
              | Some c' => cfires tm c' m tg
              | None => false
              end
  end.

Lemma cfires_complete : forall tm len c tg i ci,
  i < len -> csteps tm i c = Some ci -> cinstr ci = tg ->
  cfires tm c len tg = true.
Proof.
  induction len; intros c tg i ci Hi Hs Hq; [lia|].
  simpl. destruct i.
  - simpl in Hs. injection Hs as <-.
    apply orb_true_intro; left. apply instr_eqb_spec; assumption.
  - simpl in Hs. destruct (cstep tm c) eqn:E; [|discriminate].
    apply orb_true_intro; right.
    eapply IHlen; eauto; lia.
Qed.

Section ClosureTrEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_instr : A -> Instr.
  Variable succs : A -> option (list A).

  (** ** Computational layer (the closure search and closedness are
      Closure.v's, restated on this section's variables) *)

  Definition apool_tr (Sl : list A) : PositiveSet.t := pset_of A a_enc Sl.

  Definition mem_tr (a : A) (Sl : list A) : bool :=
    pset_mem A a_enc a (apool_tr Sl).

  Fixpoint close_tr (fuel : nat) (seen : list A) (sp : PositiveSet.t)
      (todo : list A) : option (list A) :=
    match fuel with
    | 0 => None
    | S f =>
        match todo with
        | [] => Some seen
        | a :: todo' =>
            if pset_mem A a_enc a sp then close_tr f seen sp todo'
            else match succs a with
                 | None => None
                 | Some l =>
                     close_tr f (a :: seen) (pset_add A a_enc a sp)
                       (l ++ todo')
                 end
        end
    end.

  Definition node_ok_tr (sp : PositiveSet.t) (a : A) : bool :=
    match succs a with
    | Some l => forallb (fun a' => pset_mem A a_enc a' sp) l
    | None => false
    end.

  Definition closed_tr_b (Sl : list A) : bool :=
    forallb (node_ok_tr (apool_tr Sl)) Sl.

  Definition edge_ok_tr (tg : Instr) (rnk : A -> nat) (a a' : A) : bool :=
    implb (negb (instr_eqb (a_instr a') tg)) (rnk a' <? rnk a).

  Definition rank_ok_tr (Sl : list A) (tg : Instr) (rnk : A -> nat) : bool :=
    forallb (fun a =>
      if instr_eqb (a_instr a) tg then true
      else match succs a with
           | Some l => forallb (edge_ok_tr tg rnk a) l
           | None => false
           end) Sl.

  Definition lookup_rank_tr (r : PositiveMap.tree nat) (a : A) : nat :=
    pmap_get A a_enc r a.

  Definition nontg_succs (tg : Instr) (a : A) : list A :=
    match succs a with
    | Some l => filter (fun a' => negb (instr_eqb (a_instr a') tg)) l
    | None => []
    end.

  Definition ranked_tr (r : PositiveMap.tree nat) (a : A) : bool :=
    match PositiveMap.find (a_enc a) r with
    | Some _ => true
    | None => false
    end.

  Definition peel_pass_tr (tg : Instr)
      (st : PositiveMap.tree nat * list A * bool)
      (rem : list A) : PositiveMap.tree nat * list A * bool :=
    fold_left (fun '(r, stuck, prog) a =>
      let sl := nontg_succs tg a in
      if forallb (ranked_tr r) sl
      then (PositiveMap.add (a_enc a)
              (match sl with
               | [] => 0
               | _ => S (fold_left Nat.max (map (lookup_rank_tr r) sl) 0)
               end) r, stuck, true)
      else (r, a :: stuck, prog)) rem st.

  Fixpoint peel_iter_tr (k : nat) (tg : Instr) (r : PositiveMap.tree nat)
      (rem : list A) : PositiveMap.tree nat :=
    match k, rem with
    | 0, _ | _, [] => r
    | S k', _ =>
        let '(r', stuck, prog) := peel_pass_tr tg (r, [], false) rem in
        if prog then peel_iter_tr k' tg r' stuck else r'
    end.

  Definition compute_ranks_tr (Sl : list A) (tg : Instr) : A -> nat :=
    lookup_rank_tr
      (peel_iter_tr (S (length Sl)) tg (PositiveMap.empty nat)
         (filter (fun a => negb (instr_eqb (a_instr a) tg)) Sl)).

  (** ** The checker *)

  Definition closure_check_neverqhtr (t fuel : nat) (a0 : A) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close_tr fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            forallb (fun tg =>
              if (if cfires tm c0 t tg then true
                  else existsb (fun a => instr_eqb (a_instr a) tg) Sl)
              then rank_ok_tr Sl tg (compute_ranks_tr Sl tg)
              else true) all_Instr
        | None => false
        end
    | None => false
    end.

  (** ** Logical layer *)

  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_instr : forall a c, covers a c -> a_instr a = instr_of c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  Lemma pset_mem_add_tr : forall x y s,
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

  Lemma pset_of_In_tr : forall x l,
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

  Lemma close_tr_spec_aux : forall fuel seen sp todo Sl,
    close_tr fuel seen sp todo = Some Sl ->
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
    - injection H as <-.
      split; [intro x; exact (fun h => h)|].
      split; [intros x [] |].
      intros x Hx.
      destruct (I2 x Hx) as (l & Hs & Hl).
      exists l. split; [exact Hs|].
      intros y Hy.
      destruct (Hl y Hy) as [Hm | []].
      apply I1; exact Hm.
    - destruct (pset_mem A a_enc a sp) eqn:Ea.
      + destruct (IH seen sp todo' Sl H I1) as (Ha & Hb & Hc).
        { intros x Hx.
          destruct (I2 x Hx) as (l & Hs & Hl).
          exists l. split; [exact Hs|].
          intros y Hy.
          destruct (Hl y Hy) as [Hm | [-> | Ht]];
            [left; exact Hm | left; exact Ea | right; exact Ht]. }
        split; [exact Ha|].
        split; [|exact Hc].
        intros x [-> | Hx]; [apply Ha, I1; exact Ea | exact (Hb x Hx)].
      + destruct (succs a) as [l|] eqn:Es; [|discriminate].
        destruct (IH (a :: seen) (pset_add A a_enc a sp) (l ++ todo') Sl H)
          as (Ha & Hb & Hc).
        { intros x. rewrite pset_mem_add_tr. rewrite I1.
          simpl.
          split; (intros [E | Hin]; [left; congruence | right; assumption]). }
        { intros x [<- | Hx].
          - exists l. split; [exact Es|].
            intros y Hy. right. apply in_or_app. left; exact Hy.
          - destruct (I2 x Hx) as (lx & Hsx & Hlx).
            exists lx. split; [exact Hsx|].
            intros y Hy.
            destruct (Hlx y Hy) as [Hm | [-> | Ht]].
            + left. apply pset_mem_add_tr. right; exact Hm.
            + left. apply pset_mem_add_tr. left; reflexivity.
            + right. apply in_or_app. right; exact Ht. }
        split.
        { intros x Hx. apply Ha. right; exact Hx. }
        split; [|exact Hc].
        intros x [-> | Hx].
        * apply Ha. left; reflexivity.
        * apply Hb. apply in_or_app. right; exact Hx.
  Qed.

  Lemma close_tr_root_spec : forall fuel a0 Sl,
    close_tr fuel [] PositiveSet.empty [a0] = Some Sl ->
    mem_tr a0 Sl = true /\ closed_tr_b Sl = true.
  Proof.
    intros fuel a0 Sl H.
    destruct (close_tr_spec_aux fuel [] PositiveSet.empty [a0] Sl H)
      as (_ & Hroot & Hclosed).
    { intros x. unfold pset_mem.
      split; [|intros []].
      intro Hm. apply PositiveSet.mem_spec in Hm.
      now apply PositiveSet.empty_spec in Hm. }
    { intros x []. }
    split.
    - unfold mem_tr, apool_tr. apply pset_of_In_tr.
      apply Hroot. left; reflexivity.
    - unfold closed_tr_b. apply forallb_forall.
      intros x Hx.
      destruct (Hclosed x Hx) as (l & Hs & Hl).
      unfold node_ok_tr. rewrite Hs.
      apply forallb_forall.
      intros y Hy. unfold apool_tr. apply pset_of_In_tr. exact (Hl y Hy).
  Qed.

  Lemma mem_In_tr : forall a Sl, mem_tr a Sl = true -> In a Sl.
  Proof.
    intros a Sl Hm.
    exact (pset_of_mem A a_enc a_enc_inj a Sl Hm).
  Qed.

  Lemma closed_step_tr : forall Sl a c,
    closed_tr_b Sl = true -> In a Sl -> covers a c ->
    exists c' l a', step tm c = Some c' /\ succs a = Some l /\
      In a' l /\ In a' Sl /\ covers a' c'.
  Proof.
    intros Sl a c Hcl HIn Hcov.
    assert (Hnode : node_ok_tr (apool_tr Sl) a = true).
    { unfold closed_tr_b in Hcl. rewrite forallb_forall in Hcl. auto. }
    unfold node_ok_tr in Hnode.
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    pose proof (succs_sound a c Hcov) as Hss. rewrite Es in Hss.
    destruct (step tm c) as [c'|] eqn:Est; [|contradiction].
    destruct Hss as (a' & HInl & Hcov').
    rewrite forallb_forall in Hnode.
    exists c', l, a'.
    repeat split; try assumption.
    apply mem_In_tr. unfold mem_tr. auto.
  Qed.

  Lemma closure_invariant_tr : forall Sl,
    closed_tr_b Sl = true ->
    forall a c, In a Sl -> covers a c ->
    forall k, exists c' a',
      stepn tm k c = Some c' /\ In a' Sl /\ covers a' c'.
  Proof.
    intros Sl Hcl a c HIn Hcov k.
    induction k.
    - exists c, a. split; [reflexivity | split; assumption].
    - destruct IHk as (c' & a' & Hst & HIn' & Hcov').
      destruct (closed_step_tr Sl a' c' Hcl HIn' Hcov')
        as (c'' & l & a'' & Hstep & _ & _ & HIn'' & Hcov'').
      exists c'', a''.
      split; [| split; assumption].
      replace (S k) with (k + 1) by lia.
      rewrite stepn_add, Hst. cbn [stepn]. rewrite Hstep. reflexivity.
  Qed.

  Lemma rank_find_tr : forall Sl tg rnk,
    closed_tr_b Sl = true -> rank_ok_tr Sl tg rnk = true ->
    forall r a c m, rnk a < r -> In a Sl -> covers a c ->
    stepn tm m InitES = Some c ->
    exists n, m <= n /\ FiresAt tm tg n.
  Proof.
    intros Sl tg rnk Hcl Hro.
    induction r; intros a c m Hr HIn Hcov Hm; [lia|].
    destruct (instr_eqb (a_instr a) tg) eqn:Eq.
    - apply instr_eqb_spec in Eq.
      exists m. split; [lia|].
      exists c. split; [assumption|].
      rewrite <- (covers_instr a c Hcov). assumption.
    - destruct (closed_step_tr Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      assert (Hm' : stepn tm (S m) InitES = Some c').
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (instr_eqb (a_instr a') tg) eqn:Eq'.
      + apply instr_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists c'. split; [assumption|].
        rewrite <- (covers_instr a' c' Hcov'). assumption.
      + assert (Hlt : rnk a' < rnk a).
        { unfold rank_ok_tr in Hro. rewrite forallb_forall in Hro.
          specialize (Hro a HIn). rewrite Eq, Es in Hro.
          rewrite forallb_forall in Hro.
          specialize (Hro a' HInl).
          unfold edge_ok_tr in Hro. rewrite Eq' in Hro. simpl in Hro.
          apply Nat.ltb_lt. assumption. }
        destruct (IHr a' c' (S m)) as (n & Hn & Hv);
          try assumption; try lia.
        exists n. split; [lia | assumption].
  Qed.

  Lemma rank_reach_tr : forall Sl tg rnk,
    closed_tr_b Sl = true -> rank_ok_tr Sl tg rnk = true ->
    forall r a c, rnk a < r -> In a Sl -> covers a c ->
    exists j c', stepn tm j c = Some c' /\ instr_of c' = tg.
  Proof.
    intros Sl tg rnk Hcl Hro.
    induction r as [|r IH]; intros a c Hr HIn Hcov; [lia|].
    destruct (instr_eqb (a_instr a) tg) eqn:Eq.
    - apply instr_eqb_spec in Eq.
      exists 0, c. split; [reflexivity|].
      rewrite <- (covers_instr a c Hcov). exact Eq.
    - destruct (closed_step_tr Sl a c Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (instr_eqb (a_instr a') tg) eqn:Eq'.
      + apply instr_eqb_spec in Eq'.
        exists 1, c'. split.
        * cbn [stepn]. rewrite Hstep. reflexivity.
        * rewrite <- (covers_instr a' c' Hcov'). exact Eq'.
      + assert (Hlt : rnk a' < rnk a).
        { unfold rank_ok_tr in Hro. rewrite forallb_forall in Hro.
          specialize (Hro a HIn). rewrite Eq, Es in Hro.
          rewrite forallb_forall in Hro. specialize (Hro a' HInl).
          unfold edge_ok_tr in Hro. rewrite Eq' in Hro. simpl in Hro.
          apply Nat.ltb_lt. exact Hro. }
        destruct (IH a' c' ltac:(lia) HIn' Hcov') as (j & c'' & Hsteps & Hq).
        exists (S j), c''. split; [| exact Hq].
        cbn [stepn]. rewrite Hstep. exact Hsteps.
  Qed.

  (** *** The QHBoundTr liveness gate *)

  Definition appears_tr (Sl : list A) (tg : Instr) : bool :=
    existsb (fun a => instr_eqb (a_instr a) tg) Sl.

  Definition live_ok_tr (Sl : list A) : bool :=
    forallb (fun tg =>
      if appears_tr Sl tg then rank_ok_tr Sl tg (compute_ranks_tr Sl tg)
      else true) all_Instr.

  Lemma live_fired_appears_tr : forall Sl a0 c0',
    closed_tr_b Sl = true -> In a0 Sl -> covers a0 c0' ->
    forall k c', stepn tm k c0' = Some c' ->
    appears_tr Sl (instr_of c') = true.
  Proof.
    intros Sl a0 c0' Hcl HIn Hcov k c' Hk.
    destruct (closure_invariant_tr Sl Hcl a0 c0' HIn Hcov k)
      as (c'' & a'' & Hst & HIn'' & Hcov'').
    rewrite Hk in Hst. injection Hst as <-.
    unfold appears_tr. apply existsb_exists. exists a''.
    split; [exact HIn'' |].
    apply instr_eqb_spec. apply (covers_instr a'' c' Hcov'').
  Qed.

  Lemma live_appears_recur_tr : forall Sl a0 c0' tg,
    closed_tr_b Sl = true -> live_ok_tr Sl = true ->
    In a0 Sl -> covers a0 c0' ->
    appears_tr Sl tg = true ->
    forall N, exists k c',
      N <= k /\ stepn tm k c0' = Some c' /\ instr_of c' = tg.
  Proof.
    intros Sl a0 c0' tg Hcl Hlive HIn Hcov Happ N.
    assert (Hro : rank_ok_tr Sl tg (compute_ranks_tr Sl tg) = true).
    { unfold live_ok_tr in Hlive. rewrite forallb_forall in Hlive.
      specialize (Hlive tg (all_Instr_complete tg)).
      rewrite Happ in Hlive. exact Hlive. }
    destruct (closure_invariant_tr Sl Hcl a0 c0' HIn Hcov N)
      as (cN & aN & HstN & HInN & HcovN).
    destruct (rank_reach_tr Sl tg (compute_ranks_tr Sl tg) Hcl Hro
                (S (compute_ranks_tr Sl tg aN)) aN cN
                (Nat.lt_succ_diag_r _) HInN HcovN)
      as (j & c' & Hj & Hq).
    exists (N + j), c'. split; [lia|]. split; [| exact Hq].
    rewrite stepn_add, HstN. exact Hj.
  Qed.

  (** *** Lex-gated liveness

      [live_lex_ok_tr] generalizes [live_ok_tr] exactly as Closure.v's
      [live_lex_ok] generalizes [live_ok]: each appearing instruction
      is discharged by the plain acyclicity rank OR a lexicographic
      certificate.  The certificate vocabulary and its well-foundedness
      ([lexcomp], [comp_exact], [lex_edge_decrease], [lexlt]) are
      Closure.v's own, reused by instantiation -- none of it looks at
      the target, only the guard does. *)

  Definition lex_ok_tr (Sl : list A) (tg : Instr)
      (comps : list (lexcomp A)) : bool :=
    forallb (fun a =>
      if instr_eqb (a_instr a) tg then true
      else match succs a with
           | Some l => forallb (fun a' =>
                         if instr_eqb (a_instr a') tg then true
                         else lex_edge_ok A comps a a') l
           | None => false
           end) Sl.

  Definition live_lex_ok_tr (Sl : list A)
      (cert : Instr -> list (lexcomp A)) : bool :=
    forallb (fun tg =>
      if appears_tr Sl tg
      then (if rank_ok_tr Sl tg (compute_ranks_tr Sl tg) then true
            else lex_ok_tr Sl tg (cert tg))
      else true) all_Instr.

  (** the closed-set walk tracking COMPUTABLE configurations, so
      [comp_exact]'s premises apply along the run *)
  Lemma closure_invariant_c_tr : forall Sl,
    closed_tr_b Sl = true ->
    forall a cc, In a Sl -> covers a (lift cc) ->
    forall k, exists cc' a',
      csteps tm k cc = Some cc' /\ In a' Sl /\ covers a' (lift cc').
  Proof.
    intros Sl Hcl a cc HIn Hcov k.
    induction k.
    - exists cc, a. repeat split; assumption.
    - destruct IHk as (cc' & a' & Hst & HIn' & Hcov').
      destruct (closed_step_tr Sl a' (lift cc') Hcl HIn' Hcov')
        as (c'' & l & a'' & Hstep & _ & _ & HIn'' & Hcov'').
      destruct (cstep_lift_rev tm cc' c'' Hstep) as (cc'' & Hcc'' & Hlift).
      subst c''.
      exists cc'', a''. split; [| split; assumption].
      replace (S k) with (k + 1) by lia.
      rewrite csteps_add, Hst. cbn [csteps]. rewrite Hcc''. reflexivity.
  Qed.

  Lemma lex_reach_tr : forall Sl tg comps,
    closed_tr_b Sl = true ->
    lex_ok_tr Sl tg comps = true ->
    Forall (comp_exact tm A succs covers) comps ->
    forall tuple, Acc lexlt tuple ->
    forall a cc,
    tuple = lex_tuple A comps a cc ->
    In a Sl -> covers a (lift cc) ->
    exists j c', stepn tm j (lift cc) = Some c' /\ instr_of c' = tg.
  Proof.
    intros Sl tg comps Hcl Hok Hex tuple Hacc.
    induction Hacc as [tuple Hacc IH].
    intros a cc -> HIn Hcov.
    destruct (instr_eqb (a_instr a) tg) eqn:Eq.
    - apply instr_eqb_spec in Eq.
      exists 0, (lift cc). split; [reflexivity|].
      rewrite <- (covers_instr a (lift cc) Hcov). exact Eq.
    - destruct (closed_step_tr Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      destruct (instr_eqb (a_instr a') tg) eqn:Eq'.
      + apply instr_eqb_spec in Eq'.
        exists 1, (lift cc'). split.
        * cbn [stepn]. rewrite Hstep. reflexivity.
        * rewrite <- (covers_instr a' _ Hcov'). exact Eq'.
      + assert (He : lex_edge_ok A comps a a' = true).
        { unfold lex_ok_tr in Hok. rewrite forallb_forall in Hok.
          specialize (Hok a HIn). rewrite Eq, Es in Hok.
          rewrite forallb_forall in Hok.
          specialize (Hok a' HInl). rewrite Eq' in Hok.
          simpl in Hok. exact Hok. }
        destruct (IH (lex_tuple A comps a' cc')
                    (lex_edge_decrease tm A succs covers comps a cc a' cc' l
                       Hex Hcov Hcov' Hcc' Es HInl He)
                    a' cc' eq_refl HIn' Hcov')
          as (j & c'' & Hj & Hq).
        exists (S j), c''. split; [| exact Hq].
        cbn [stepn]. rewrite Hstep. exact Hj.
  Qed.

  Lemma live_appears_recur_lex_tr : forall Sl cert a0 cc0 tg,
    closed_tr_b Sl = true ->
    Forall (comp_exact tm A succs covers) (cert tg) ->
    live_lex_ok_tr Sl cert = true ->
    In a0 Sl -> covers a0 (lift cc0) ->
    appears_tr Sl tg = true ->
    forall N, exists k c',
      N <= k /\ stepn tm k (lift cc0) = Some c' /\ instr_of c' = tg.
  Proof.
    intros Sl cert a0 cc0 tg Hcl Hex Hlive HIn Hcov Happ N.
    destruct (closure_invariant_c_tr Sl Hcl a0 cc0 HIn Hcov N)
      as (ccN & aN & HstN & HInN & HcovN).
    assert (HstN' : stepn tm N (lift cc0) = Some (lift ccN))
      by (apply csteps_lift; exact HstN).
    unfold live_lex_ok_tr in Hlive. rewrite forallb_forall in Hlive.
    specialize (Hlive tg (all_Instr_complete tg)). rewrite Happ in Hlive.
    simpl in Hlive. apply orb_true_iff in Hlive as [Hro | Hlex].
    - destruct (rank_reach_tr Sl tg (compute_ranks_tr Sl tg) Hcl Hro
                  (S (compute_ranks_tr Sl tg aN)) aN (lift ccN)
                  (Nat.lt_succ_diag_r _) HInN HcovN)
        as (j & c' & Hj & Hq).
      exists (N + j), c'. split; [lia|]. split; [| exact Hq].
      rewrite stepn_add, HstN'. exact Hj.
    - destruct (lex_reach_tr Sl tg (cert tg) Hcl Hlex Hex
                  (lex_tuple A (cert tg) aN ccN)
                  (lexlt_wf_len (length (lex_tuple A (cert tg) aN ccN)) _
                     eq_refl)
                  aN ccN eq_refl HInN HcovN)
        as (j & c' & Hj & Hq).
      exists (N + j), c'. split; [lia|]. split; [| exact Hq].
      rewrite stepn_add, HstN'. exact Hj.
  Qed.

  (** the [rank_find_tr]-shaped variant: absolute step indices from
      [InitES], for the never-QH checker *)
  Lemma lex_find_tr : forall Sl tg comps,
    closed_tr_b Sl = true ->
    lex_ok_tr Sl tg comps = true ->
    Forall (comp_exact tm A succs covers) comps ->
    forall tuple, Acc lexlt tuple ->
    forall a cc m,
    tuple = lex_tuple A comps a cc ->
    In a Sl -> covers a (lift cc) ->
    stepn tm m InitES = Some (lift cc) ->
    exists n', m <= n' /\ FiresAt tm tg n'.
  Proof.
    intros Sl tg comps Hcl Hok Hex tuple Hacc.
    induction Hacc as [tuple Hacc IH].
    intros a cc m -> HIn Hcov Hm.
    destruct (instr_eqb (a_instr a) tg) eqn:Eq.
    - apply instr_eqb_spec in Eq.
      exists m. split; [lia|].
      exists (lift cc). split; [assumption|].
      rewrite <- (covers_instr a (lift cc) Hcov). assumption.
    - destruct (closed_step_tr Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      assert (Hm' : stepn tm (S m) InitES = Some (lift cc')).
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (instr_eqb (a_instr a') tg) eqn:Eq'.
      + apply instr_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists (lift cc'). split; [assumption|].
        rewrite <- (covers_instr a' _ Hcov'). assumption.
      + assert (He : lex_edge_ok A comps a a' = true).
        { unfold lex_ok_tr in Hok. rewrite forallb_forall in Hok.
          specialize (Hok a HIn). rewrite Eq, Es in Hok.
          rewrite forallb_forall in Hok.
          specialize (Hok a' HInl). rewrite Eq' in Hok.
          simpl in Hok. assumption. }
        destruct (IH (lex_tuple A comps a' cc')
                    (lex_edge_decrease tm A succs covers comps a cc a' cc' l
                       Hex Hcov Hcov' Hcc' Es HInl He)
                    a' cc' (S m) eq_refl HIn' Hcov' Hm')
          as (n' & Hn' & Hv).
        exists n'. split; [lia | assumption].
  Qed.

  (** the lex-gated never-QH closure check ([closure_check_neverqhtr]
      with each fired instruction discharged by a certificate) *)
  Definition closure_check_neverqhtr_lex (t fuel : nat) (a0 : A)
      (cert : Instr -> list (lexcomp A)) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close_tr fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            forallb (fun tg =>
              if (if cfires tm c0 t tg then true
                  else existsb (fun a => instr_eqb (a_instr a) tg) Sl)
              then lex_ok_tr Sl tg (cert tg)
              else true) all_Instr
        | None => false
        end
    | None => false
    end.

  Theorem closure_check_neverqhtr_lex_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall tg, Forall (comp_exact tm A succs covers) (cert tg)) ->
    closure_check_neverqhtr_lex t fuel a0 cert = true ->
    NeverQuasiHaltsTr tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqhtr_lex in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close_tr fuel [] PositiveSet.empty [a0]) as [Sl|] eqn:Hcls;
      [|discriminate].
    rename H into Hq.
    destruct (close_tr_root_spec fuel a0 Sl Hcls) as [Hin Hcl].
    apply mem_In_tr in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros tg Hvq N.
    assert (Hro : lex_ok_tr Sl tg (cert tg) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq tg (all_Instr_complete tg)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : (if cfires tm c0 t tg then true
                       else existsb (fun a => instr_eqb (a_instr a) tg) Sl)
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant_tr Sl Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply instr_eqb_spec. rewrite (covers_instr a' c' Hcov').
          assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cfires_complete; [exact Hlt | exact Hcn' |].
          rewrite <- cinstr_lift. exact Hqn. }
      rewrite Hprem in Hq.
      destruct (lex_ok_tr Sl tg (cert tg)); [reflexivity | discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant_tr Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (lex_find_tr Sl tg (cert tg) Hcl Hro (Hcert tg)
                (lex_tuple A (cert tg) aM ccM)
                (lexlt_wf_len (length (lex_tuple A (cert tg) aM ccM)) _
                   eq_refl)
                aM ccM M eq_refl HInM HcovM HM)
      as (n & Hn & Hv).
    exists n. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

  Theorem closure_check_neverqhtr_sound : forall t fuel a0,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    closure_check_neverqhtr t fuel a0 = true -> NeverQuasiHaltsTr tm.
  Proof.
    intros t fuel a0 Hstart H. unfold closure_check_neverqhtr in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close_tr fuel [] PositiveSet.empty [a0]) as [Sl|] eqn:Hcls;
      [|discriminate].
    rename H into Hq.
    destruct (close_tr_root_spec fuel a0 Sl Hcls) as [Hin Hcl].
    apply mem_In_tr in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros tg Hvq N.
    assert (Hro : rank_ok_tr Sl tg (compute_ranks_tr Sl tg) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq tg (all_Instr_complete tg)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : (if cfires tm c0 t tg then true
                       else existsb (fun a => instr_eqb (a_instr a) tg) Sl)
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant_tr Sl Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply instr_eqb_spec. rewrite (covers_instr a' c' Hcov').
          assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cfires_complete; [exact Hlt | exact Hcn' |].
          rewrite <- cinstr_lift. exact Hqn. }
      rewrite Hprem in Hq. destruct (rank_ok_tr Sl tg (compute_ranks_tr Sl tg));
        [reflexivity | discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant_tr Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (rank_find_tr Sl tg (compute_ranks_tr Sl tg) Hcl Hro
                (S (compute_ranks_tr Sl tg aM)) aM cM M)
      as (n & Hn & Hv); try assumption; try lia.
    exists n. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End ClosureTrEngine.
