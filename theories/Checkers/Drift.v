(** * Drift: the per-SCC NET-drift rule (c3) inside the lex engine.

    Rule (c2) (FuelSCC.v) kills a stuck SCC whose alive intra-edges
    ALL move the head right with right fuel.  The post-fuel survivors
    (the harness's 17 [neverqh_drift] certificates) are mixed-direction
    zig-zag consume/refill cycles: no uniform direction exists, but
    every CYCLE of the SCC has strictly positive net displacement
    toward one side, and every context moving TOWARD that side holds
    fuel there.  Rule (c3) kills those too.

    This file integrates rule (c3) into the lexicographic gate the way
    FuelSCC.v integrates (c2), with two changes:

    - the runner gate becomes a DRIFT gate carrying untrusted per-node
      potentials [phi] and a scale [W]: a gate-internal edge [a -> a']
      must satisfy [phi a' + 1 <= phi a + W] when [a] moves toward the
      drift side and [phi a' + W + 1 <= phi a] when it moves away.
      Telescoping around a cycle with [k] edges gives
      [W * net >= k >= 1], so feasible potentials exist exactly for
      SCCs all of whose cycles net strictly toward the side (the
      generator finds them by Bellman-Ford; a wrong table merely fails
      the edge re-check);

    - there are TWO gates per state, one per drift side, DISJOINT
      (checked).  This is load-bearing: two of the 17 machines have a
      single state whose stuck SCCs drift OPPOSITE ways, so no global
      orientation (mirroring) can serve them.

    Soundness is the record argument made into a descent: along a
    gate-internal stretch the natural measure [W * R + phi a] (R = the
    toward-side window bound of Records.v) drops by at least 1 every
    step -- a toward-move shrinks the window exactly by 1 (fuel keeps
    the window positive, [has_right_nonblank_window_pos]), an
    away-move grows it by exactly 1 and the potential pays [W + 1].
    So a confined run would drive a nat below 0: the head cannot
    diverge toward a side it keeps fuel on, because a diverging head
    keeps entering never-visited (hence blank) territory.  Fuel is
    only demanded of TOWARD-moving gate nodes -- away-movers need
    nothing -- which is weaker than the C rule's premise, so
    everything it certified passes.

    Gate disjointness makes a stretch unable to switch gates without a
    lex-good edge (the edge check requires BOTH endpoints in one
    gate), so at most one side's budget is live at any node and the
    two budgets collapse into one selector ([dbudget]).  The descent
    is then structurally FuelSCC's: an outer induction on [Acc lexlt]
    handles lex-good edges (with fresh window bounds from the step
    index), an inner induction on the single nat budget handles gate
    stretches, and [lexle] carries the non-increase bookkeeping.

    Everything emitted by the generator (gates, potentials, W, lex
    tables) is UNTRUSTED data re-checked here node by node and edge by
    edge.  The instance at the bottom runs on the class-refined
    contexts of FuelWide.v ([fcconf]), reusing its successor relation,
    covering proofs and certificate vocabulary unchanged. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import Cycle ExactClosure NGram Fuel FuelClass
  FuelSCC FuelWide.
Import ListNotations.

(** ** Left-side record vocabulary (mirrors of Records.v's right side) *)

Definition steps_left (tm : TM) (c : ExecState) : Prop :=
  exists tr, tm (fst c) (t_head (snd c)) = Some tr /\ t_dir tr = DL.

Definition has_left_nonblank (tp : Tape) : Prop :=
  exists j, t_left tp j <> S0.

Lemma has_left_nonblank_window_pos : forall tp L,
  left_bounded tp L -> has_left_nonblank tp -> 1 <= L.
Proof.
  intros tp L HL [j Hj]. destruct L as [|L']; [|lia].
  exfalso. apply Hj, HL. lia.
Qed.

(** The four step/window interactions on [ExecState]: a move shrinks
    the window it walks into and grows the one it leaves behind
    ([step_shrinks_es] of FuelSCC.v is the right/right case). *)

Lemma step_left_shrinks_es : forall tm c c' L,
  step tm c = Some c' -> steps_left tm c ->
  left_bounded (snd c) L -> left_bounded (snd c') (Nat.pred L).
Proof.
  intros tm [q1 tp1] [q2 tp2] L Hst [tr [Etm Ed]] HL.
  unfold step in Hst. simpl in Etm. rewrite Etm in Hst.
  injection Hst as _ <-. rewrite Ed.
  apply move_DL_left; exact HL.
Qed.

Lemma step_left_grows_right_es : forall tm c c' R,
  step tm c = Some c' -> steps_left tm c ->
  right_bounded (snd c) R -> right_bounded (snd c') (S R).
Proof.
  intros tm [q1 tp1] [q2 tp2] R Hst [tr [Etm Ed]] HR.
  unfold step in Hst. simpl in Etm. rewrite Etm in Hst.
  injection Hst as _ <-. rewrite Ed.
  apply move_DL_right; exact HR.
Qed.

Lemma step_right_grows_left_es : forall tm c c' L,
  step tm c = Some c' -> steps_right tm c ->
  left_bounded (snd c) L -> left_bounded (snd c') (S L).
Proof.
  intros tm [q1 tp1] [q2 tp2] L Hst [tr [Etm Ed]] HL.
  unfold step in Hst. simpl in Etm. rewrite Etm in Hst.
  injection Hst as _ <-. rewrite Ed.
  apply move_DR_left; exact HL.
Qed.

Section DriftEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).
  Variable node_moves_right : A -> bool.
  Variable node_moves_left : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.
  Variable node_lfuel_ge1 : A -> bool.

  (** ** The checker *)

  (** Potential inequality across a gate-internal edge, selected by
      the SOURCE node's move: a toward-move may raise [phi] by up to
      [W - 1], an away-move must drop it by at least [W + 1]. *)
  Definition dpot_okR (phi : A -> nat) (W : nat) (a a' : A) : bool :=
    if node_moves_right a then phi a' + 1 <=? phi a + W
    else phi a' + W + 1 <=? phi a.

  Definition dpot_okL (phi : A -> nat) (W : nat) (a a' : A) : bool :=
    if node_moves_left a then phi a' + 1 <=? phi a + W
    else phi a' + W + 1 <=? phi a.

  Definition drift_edge_ok (comps : list (lexcomp A))
      (rgR rgL : A -> bool) (phiR phiL : A -> nat) (W : nat)
      (a a' : A) : bool :=
    lex_edge_ok A comps a a'
    || (lex_noninc_all A comps a a'
        && (rgR a && rgR a' && dpot_okR phiR W a a'
            || rgL a && rgL a' && dpot_okL phiL W a a')).

  (** Gate node facts: never state [q]; the two gates disjoint; a
      node moving toward the gate's side holds that side's fuel, a
      node moving away just has a determined away-move. *)
  Definition dgate_ok (Sl : list A) (q : St) (rgR rgL : A -> bool)
      : bool :=
    forallb (fun a =>
      implb (rgR a)
            (negb (st_eqb (a_state a) q) && negb (rgL a)
             && (node_moves_right a && node_rfuel_ge1 a
                 || negb (node_moves_right a) && node_moves_left a))
      && implb (rgL a)
               (negb (st_eqb (a_state a) q)
                && (node_moves_left a && node_lfuel_ge1 a
                    || negb (node_moves_left a) && node_moves_right a)))
      Sl.

  Definition drift_state_ok (Sl : list A) (q : St)
      (comps : list (lexcomp A)) (rgR rgL : A -> bool)
      (phiR phiL : A -> nat) (W : nat) : bool :=
    dgate_ok Sl q rgR rgL &&
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else match succs a with
           | Some l => forallb (fun a' =>
                         st_eqb (a_state a') q
                         || drift_edge_ok comps rgR rgL phiR phiL W a a')
                         l
           | None => false
           end) Sl.

  Definition dcert : Type :=
    (list (lexcomp A) * (A -> bool) * (A -> nat)
     * (A -> bool) * (A -> nat) * nat)%type.

  Definition closure_check_neverqh_drift (t fuel : nat) (a0 : A)
      (cert : St -> dcert) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            closed_b A a_enc succs Sl && mem A a_enc a0 Sl &&
            forallb (fun q =>
              implb (cvisits tm c0 t q
                     || existsb (fun a => st_eqb (a_state a) q) Sl)
                    (let '(comps, rgR, phiR, rgL, phiL, W) := cert q in
                     drift_state_ok Sl q comps rgR rgL phiR phiL W))
                    all_St
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
  Hypothesis node_moves_right_sound : forall a c,
    node_moves_right a = true -> covers a c -> steps_right tm c.
  Hypothesis node_moves_left_sound : forall a c,
    node_moves_left a = true -> covers a c -> steps_left tm c.
  Hypothesis node_rfuel_ge1_sound : forall a c,
    node_rfuel_ge1 a = true -> covers a c -> has_right_nonblank (snd c).
  Hypothesis node_lfuel_ge1_sound : forall a c,
    node_lfuel_ge1 a = true -> covers a c -> has_left_nonblank (snd c).

  (** ** The descent

      At most one side's budget is live at any node (the gates are
      disjoint), so one nat carries the whole gate-stretch descent. *)

  Definition dbudget (rgR rgL : A -> bool) (phiR phiL : A -> nat)
      (W : nat) (a : A) (R L : nat) : nat :=
    if rgR a then W * R + phiR a
    else if rgL a then W * L + phiL a else 0.

  (** Outer induction: accessibility of the lex tuple bound [T0]
      (strict drops = lex-good edges, which also refresh the window
      bounds from the step index).  Inner induction: the drift budget
      [dbudget _ _ _ _ _ a R L < v], which every gate-internal edge
      strictly decreases. *)
  Lemma drift_find : forall Sl q comps rgR rgL phiR phiL W,
    closed_b A a_enc succs Sl = true ->
    drift_state_ok Sl q comps rgR rgL phiR phiL W = true ->
    Forall (comp_exact tm A succs covers) comps ->
    forall T0, Acc lexlt T0 ->
    forall v a cc m R L,
    lexle (lex_tuple A comps a cc) T0 ->
    right_bounded (snd (lift cc)) R ->
    left_bounded (snd (lift cc)) L ->
    dbudget rgR rgL phiR phiL W a R L < v ->
    In a Sl -> covers a (lift cc) ->
    stepn tm m InitES = Some (lift cc) ->
    exists n', m <= n' /\ VisitsAt tm q n'.
  Proof.
    intros Sl q comps rgR rgL phiR phiL W Hcl Hok Hex.
    apply andb_prop in Hok as [Hgate Hedges].
    assert (Hgspec : forall a, In a Sl ->
      (rgR a = true ->
       st_eqb (a_state a) q = false /\ rgL a = false /\
       (node_moves_right a && node_rfuel_ge1 a
        || negb (node_moves_right a) && node_moves_left a) = true) /\
      (rgL a = true ->
       st_eqb (a_state a) q = false /\
       (node_moves_left a && node_lfuel_ge1 a
        || negb (node_moves_left a) && node_moves_right a) = true)).
    { intros a HIn.
      unfold dgate_ok in Hgate. rewrite forallb_forall in Hgate.
      specialize (Hgate a HIn).
      apply andb_prop in Hgate as [HgR HgL].
      split.
      - intros Ha. rewrite Ha in HgR. simpl in HgR.
        apply andb_prop in HgR as [HgR Hnode].
        apply andb_prop in HgR as [Hq' Hdisj].
        rewrite negb_true_iff in Hq', Hdisj.
        repeat split; assumption.
      - intros Ha. rewrite Ha in HgL. simpl in HgL.
        apply andb_prop in HgL as [Hq' Hnode].
        rewrite negb_true_iff in Hq'.
        split; assumption. }
    intros T0 Hacc.
    induction Hacc as [T0 _ IHT].
    induction v as [|v IHv]; intros a cc m R L Hle HR HL Hv HIn Hcov Hm;
      [lia|].
    destruct (st_eqb (a_state a) q) eqn:Eq.
    - (* the covered node itself is a q-visit *)
      apply st_eqb_spec in Eq.
      exists m. split; [lia|].
      exists (lift cc). split; [assumption|].
      rewrite <- (covers_state a (lift cc) Hcov). assumption.
    - destruct (closed_step tm A a_enc succs covers a_enc_inj succs_sound
                  Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      assert (Hm' : stepn tm (S m) InitES = Some (lift cc')).
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (extent_le_steps tm (S m) (lift cc') Hm') as [HRf HLf].
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists (lift cc'). split; [assumption|].
        rewrite <- (covers_state a' _ Hcov'). assumption.
      + assert (He : drift_edge_ok comps rgR rgL phiR phiL W a a' = true).
        { rewrite forallb_forall in Hedges.
          specialize (Hedges a HIn). rewrite Eq, Es in Hedges.
          rewrite forallb_forall in Hedges.
          specialize (Hedges a' HInl). rewrite Eq' in Hedges.
          simpl in Hedges. exact Hedges. }
        apply orb_prop in He as [Hlex | Hdrift].
        * (* lex-good edge: strict drop below T0, fresh budget from
             the step index *)
          assert (Hlt : lexlt (lex_tuple A comps a' cc')
                              (lex_tuple A comps a cc))
            by (eapply lex_edge_decrease; eauto).
          assert (Hlt0 : lexlt (lex_tuple A comps a' cc') T0)
            by (eapply lexlt_lexle_trans; eassumption).
          destruct (IHT _ Hlt0
                      (S (dbudget rgR rgL phiR phiL W a' (S m) (S m)))
                      a' cc' (S m) (S m) (S m)
                      (lexle_refl _) HRf HLf
                      (Nat.lt_succ_diag_r _)
                      HIn' Hcov' Hm') as (n' & Hn' & Hv').
          exists n'. split; [lia | assumption].
        * (* gate-internal edge: the budget strictly decreases *)
          apply andb_prop in Hdrift as [Hni Hgates].
          assert (Hle' : lexle (lex_tuple A comps a' cc')
                               (lex_tuple A comps a cc))
            by (eapply tuple_noninc_lexle; eauto).
          assert (Hle0 : lexle (lex_tuple A comps a' cc') T0)
            by (eapply lexle_trans; eassumption).
          apply orb_prop in Hgates as [HgR | HgL].
          -- (* right-drift gate *)
             apply andb_prop in HgR as [HgR Hpot].
             apply andb_prop in HgR as [Hga Hga'].
             destruct (proj1 (Hgspec a HIn) Hga) as (_ & _ & Hnode).
             unfold dbudget in Hv. rewrite Hga in Hv.
             unfold dpot_okR in Hpot.
             assert (Hrec : W * (if node_moves_right a
                                 then Nat.pred R else S R) + phiR a' < v
                            /\ right_bounded (snd (lift cc'))
                                 (if node_moves_right a
                                  then Nat.pred R else S R)).
             { destruct (node_moves_right a) eqn:Emv;
                 simpl in Hnode, Hpot; apply Nat.leb_le in Hpot.
               - rewrite orb_false_r in Hnode.
                 assert (Hsr : steps_right tm (lift cc))
                   by (eapply node_moves_right_sound; eauto).
                 assert (Hnb : has_right_nonblank (snd (lift cc)))
                   by (eapply node_rfuel_ge1_sound; eauto).
                 assert (HR1 : 1 <= R)
                   by (eapply has_right_nonblank_window_pos; eauto).
                 split.
                 + destruct R as [|R0]; [lia|]. simpl. nia.
                 + eapply step_shrinks_es; eauto.
               - assert (Hsl : steps_left tm (lift cc))
                   by (eapply node_moves_left_sound; eauto).
                 split.
                 + rewrite Nat.mul_succ_r. lia.
                 + eapply step_left_grows_right_es; eauto. }
             destruct Hrec as [Hv2 HR'].
             assert (Hb' : dbudget rgR rgL phiR phiL W a'
                             (if node_moves_right a
                              then Nat.pred R else S R) (S m) < v)
               by (unfold dbudget; rewrite Hga'; exact Hv2).
             destruct (IHv a' cc' (S m)
                         (if node_moves_right a
                          then Nat.pred R else S R) (S m)
                         Hle0 HR' HLf Hb' HIn' Hcov' Hm')
               as (n' & Hn' & Hvis).
             exists n'. split; [lia | assumption].
          -- (* left-drift gate *)
             apply andb_prop in HgL as [HgL Hpot].
             apply andb_prop in HgL as [Hga Hga'].
             destruct (proj2 (Hgspec a HIn) Hga) as (_ & Hnode).
             assert (HdisjA : rgR a = false).
             { destruct (rgR a) eqn:E; [|reflexivity].
               destruct (proj1 (Hgspec a HIn) E) as (_ & HL2 & _).
               congruence. }
             assert (HdisjA' : rgR a' = false).
             { destruct (rgR a') eqn:E; [|reflexivity].
               destruct (proj1 (Hgspec a' HIn') E) as (_ & HL2 & _).
               congruence. }
             unfold dbudget in Hv. rewrite HdisjA, Hga in Hv.
             unfold dpot_okL in Hpot.
             assert (Hrec : W * (if node_moves_left a
                                 then Nat.pred L else S L) + phiL a' < v
                            /\ left_bounded (snd (lift cc'))
                                 (if node_moves_left a
                                  then Nat.pred L else S L)).
             { destruct (node_moves_left a) eqn:Emv;
                 simpl in Hnode, Hpot; apply Nat.leb_le in Hpot.
               - rewrite orb_false_r in Hnode.
                 assert (Hsl : steps_left tm (lift cc))
                   by (eapply node_moves_left_sound; eauto).
                 assert (Hnb : has_left_nonblank (snd (lift cc)))
                   by (eapply node_lfuel_ge1_sound; eauto).
                 assert (HL1 : 1 <= L)
                   by (eapply has_left_nonblank_window_pos; eauto).
                 split.
                 + destruct L as [|L0]; [lia|]. simpl. nia.
                 + eapply step_left_shrinks_es; eauto.
               - assert (Hsr : steps_right tm (lift cc))
                   by (eapply node_moves_right_sound; eauto).
                 split.
                 + rewrite Nat.mul_succ_r. lia.
                 + eapply step_right_grows_left_es; eauto. }
             destruct Hrec as [Hv2 HL'].
             assert (Hb' : dbudget rgR rgL phiR phiL W a' (S m)
                             (if node_moves_left a
                              then Nat.pred L else S L) < v)
               by (unfold dbudget; rewrite HdisjA', Hga'; exact Hv2).
             destruct (IHv a' cc' (S m) (S m)
                         (if node_moves_left a
                          then Nat.pred L else S L)
                         Hle0 HRf HL' Hb' HIn' Hcov' Hm')
               as (n' & Hn' & Hvis).
             exists n'. split; [lia | assumption].
  Qed.

  (** ** Soundness of the checker *)

  Theorem closure_check_neverqh_drift_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall (comp_exact tm A succs covers)
                      (fst (fst (fst (fst (fst (cert q))))))) ->
    closure_check_neverqh_drift t fuel a0 cert = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqh_drift in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0])
      as [Sl|]; [|discriminate].
    apply andb_prop in H as [H Hq].
    apply andb_prop in H as [Hcl Hin].
    apply (mem_In A a_enc a_enc_inj) in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    destruct (cert q) as [[[[[comps rgR] phiR] rgL] phiL] W] eqn:Ec.
    assert (Hlive : drift_state_ok Sl q comps rgR rgL phiR phiL W = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_St_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cvisits tm c0 t q
                      || existsb (fun a => st_eqb (a_state a) q) Sl = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant tm A a_enc succs covers a_enc_inj
                      succs_sound Sl Hcl a0 (lift ct)
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
      rewrite Hprem, Ec in Hq. exact Hq. }
    set (M := Nat.max N t).
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj
                succs_sound Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (extent_le_steps tm M (lift ccM) HM) as [HRM HLM].
    assert (Hcomps : Forall (comp_exact tm A succs covers) comps).
    { specialize (Hcert q). rewrite Ec in Hcert. exact Hcert. }
    destruct (drift_find Sl q comps rgR rgL phiR phiL W Hcl Hlive Hcomps
                (lex_tuple A comps aM ccM)
                (lexlt_wf_len
                   (length (lex_tuple A comps aM ccM)) _ eq_refl)
                (S (dbudget rgR rgL phiR phiL W aM M M))
                aM ccM M M M (lexle_refl _) HRM HLM
                (Nat.lt_succ_diag_r _) HInM HcovM HM)
      as (n' & Hn' & Hv).
    exists n'. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End DriftEngine.

(** ** The class-refined instance (FuelWide contexts)

    Everything is FuelWide's: the refined contexts [fcconf], their
    encoding, successor relation, covering and certificate
    vocabulary.  Only the two LEFT-side node predicates are new. *)

Definition fnode_moves_left (tm : TM) (a : cconf) : bool :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | Some tr => match t_dir tr with DL => true | DR => false end
  | None => false
  end.

Definition fnode_lfuel_ge1 (a : cconf) : bool :=
  let '(q, (lw, s, rw)) := a in
  existsb (fun x => negb (sym_eqb x S0)) lw.

Lemma fnode_moves_left_sound : forall tm n lset rset a c,
  fnode_moves_left tm a = true ->
  ng_covers n lset rset a c ->
  steps_left tm c.
Proof.
  intros tm n lset rset [q [[lw s] rw]] c Hml Hcov.
  destruct Hcov as (Hq & Hh & _).
  unfold fnode_moves_left in Hml.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  destruct (t_dir tr) eqn:Ed; [|discriminate].
  unfold steps_left. exists tr.
  rewrite <- Hq, <- Hh in Etr. split; [exact Etr | exact Ed].
Qed.

Lemma fnode_lfuel_ge1_sound : forall n lset rset a c,
  fnode_lfuel_ge1 a = true ->
  ng_covers n lset rset a c ->
  has_left_nonblank (snd c).
Proof.
  intros n lset rset [q [[lw s] rw]] c Hlf Hcov.
  destruct Hcov as (_ & _ & Hlw & _).
  unfold fnode_lfuel_ge1 in Hlf.
  apply existsb_exists in Hlf as (x & Hin & Hnb).
  rewrite Hlw in Hin. unfold win in Hin.
  apply in_map_iff in Hin as (k & Hk & _).
  apply negb_true_iff in Hnb.
  exists k. intro Hcontra.
  rewrite Hk in Hcontra.
  apply (proj2 (sym_eqb_spec x S0)) in Hcontra.
  rewrite Hcontra in Hnb. discriminate.
Qed.

Definition fwnode_moves_left (tm : TM) (a : fcconf) : bool :=
  fnode_moves_left tm (fst a).

Definition fwnode_lfuel_ge1 (a : fcconf) : bool :=
  fnode_lfuel_ge1 (fst a) || fc_ge1 (fst (snd a)).

Lemma fwnode_moves_left_sound : forall tm n lset rset a c,
  fwnode_moves_left tm a = true ->
  fw_covers n lset rset a c ->
  steps_left tm c.
Proof.
  intros tm n lset rset a c H (Hng & _ & _).
  exact (fnode_moves_left_sound tm n lset rset (fst a) c H Hng).
Qed.

Lemma fwnode_lfuel_ge1_sound : forall n lset rset a c,
  fwnode_lfuel_ge1 a = true ->
  fw_covers n lset rset a c ->
  has_left_nonblank (snd c).
Proof.
  intros n lset rset [b [fl fr]] c H (Hng & Hcl & _).
  unfold fwnode_lfuel_ge1 in H. simpl in H, Hcl.
  apply orb_prop in H as [Hw | Hc].
  - exact (fnode_lfuel_ge1_sound n lset rset b c Hw Hng).
  - exact (fc_ge1_sound fl (t_left (snd c)) Hcl Hc).
Qed.

(** ** Certificate denotation: refined-key tables, base measures *)

Definition dw_cert : Type :=
  (list ngcomp * list positive * list (positive * nat)
   * list positive * list (positive * nat) * nat)%type.

Definition dw_cert_denote (tm : TM) (n : nat) (ct : dw_cert)
    : dcert fcconf :=
  let '(comps, gR, phiR, gL, phiL, W) := ct in
  (map (fw_comp_denote tm n) comps,
   (let s := psete_of gR in
    fun a => PositiveSet.mem (fcconf_enc a) s),
   fpmape_get (pmape_of phiR),
   (let s := psete_of gL in
    fun a => PositiveSet.mem (fcconf_enc a) s),
   fpmape_get (pmape_of phiL),
   W).

(** ** The checker *)

Definition ngram_check_neverqh_driftw (tm : TM) (n t fuel rounds : nat)
    (cert : St -> dw_cert) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_drift tm fcconf fcconf_enc fw_state
        (fw_succs tm lset rset)
        (fwnode_moves_right tm) (fwnode_moves_left tm)
        fwnode_rfuel_ge1 fwnode_lfuel_ge1
        t fuel (fw_start n cc)
        (fun q => dw_cert_denote tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_driftw_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_driftw tm n t fuel rounds cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_driftw in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_drift_sound tm fcconf fcconf_enc fw_state
           (fw_succs tm lset rset)
           (fwnode_moves_right tm) (fwnode_moves_left tm)
           fwnode_rfuel_ge1 fwnode_lfuel_ge1
           (fw_covers n lset rset)) in Hcheck;
    [assumption | | | | | | | | |].
  - exact fcconf_enc_inj.
  - intros a c Hc. eapply fw_covers_state; eauto.
  - intros a c Hc. apply fw_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound; eauto.
  - intros a c Hml Hc. eapply fwnode_moves_left_sound; eauto.
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound; eauto.
  - intros a c Hlf Hc. eapply fwnode_lfuel_ge1_sound; eauto.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply fw_start_covers. exact Hseed.
  - intros q0.
    destruct (cert q0) as [[[[[comps gR] phiR] gL] phiL] W].
    apply Forall_forall. intros comp Hin.
    simpl in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (ngm_exact tm n lset rset m (fst a) cc (fst a') cc' Hn
               (proj1 Hca) Hstep).
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (pm_exact tm n lset rset pp rg (fst a) cc (fst a') cc');
        try assumption.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
      * exact (proj1 Hca).
Qed.
