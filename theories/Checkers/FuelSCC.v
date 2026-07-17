(** * FuelSCC: the per-SCC runner rule (c2) inside the lex engine.

    The engine's combined fuel checker ([closure_check_neverqh_fuel],
    Closure.v) gates each state by [lex_ok || runner_ok], where the
    runner disjunct demands the WHOLE q-avoiding closure be a fueled
    right-mover.  Real fuel machines are not like that: rank measures
    peel most of the graph and the runner argument is only needed on
    the residual SCCs (verify.c applies rule (c2) per SCC inside its
    peeling loop).  This file integrates the runner rule into the
    LEXICOGRAPHIC gate instead:

      every q-avoiding edge is either lex-good ([lex_edge_ok]) or
      RUNNER-INTERNAL -- both endpoints in an untrusted "runner gate"
      set whose nodes all move right with fuel, with every lex
      component non-increasing across the edge.

    Soundness composes the two existing descent arguments.  Along an
    infinite q-avoiding covered run the lex tuple never increases
    (non-increasing across runner edges, strictly decreasing across
    lex-good ones), so by well-foundedness of [lexlt] the run can use
    lex-good edges only finitely often; once they stop, every step is
    runner-internal, the head moves right forever with right fuel,
    and the record bound ([extent_le_steps] / [step_right_shrinks])
    drives the right window to zero while the fuel keeps it positive
    -- impossible.  Formally: an outer induction on [Acc lexlt] handles
    lex-good edges (with a FRESH window bound from the current step
    index), an inner induction on the window bound handles runner
    stretches, and [lexle] (the reflexive order) carries the
    non-increase bookkeeping between the two.

    The gate set is UNTRUSTED data (an encoded-key set in generated
    certificates): [rgate_ok] re-checks the node facts and
    [fscc_edge_ok] re-checks every edge, so a wrong gate merely fails
    the check.  Left-runners go through [mirror_never_qh] as usual. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

(** ** [lexle]: the reflexive closure of [lexlt] *)

Definition lexle (xs ys : list nat) : Prop := lexlt xs ys \/ xs = ys.

Lemma lexle_refl : forall xs, lexle xs xs.
Proof. intros xs. right. reflexivity. Qed.

Lemma lexlt_trans : forall xs ys zs,
  lexlt xs ys -> lexlt ys zs -> lexlt xs zs.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] [|z zs] H1 H2;
    simpl in *; try contradiction.
  destruct H1 as [[Hxy L1] | [-> H1]]; destruct H2 as [[Hyz L2] | [-> H2]].
  - left. split; [lia | congruence].
  - left. split; [assumption | rewrite L1; apply lexlt_length; assumption].
  - left. split; [assumption | rewrite <- L2; apply lexlt_length; assumption].
  - right. split; [reflexivity | eapply IH; eassumption].
Qed.

Lemma lexlt_lexle_trans : forall xs ys zs,
  lexlt xs ys -> lexle ys zs -> lexlt xs zs.
Proof.
  intros xs ys zs H1 [H2 | <-]; [eapply lexlt_trans; eassumption | exact H1].
Qed.

Lemma lexle_trans : forall xs ys zs,
  lexle xs ys -> lexle ys zs -> lexle xs zs.
Proof.
  intros xs ys zs [H1 | <-] H2; [| exact H2].
  left. eapply lexlt_lexle_trans; eassumption.
Qed.

Section FuelSCCEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).
  Variable node_moves_right : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.

  (** ** The checker *)

  Definition lex_noninc_all (comps : list (lexcomp A)) (a a' : A) : bool :=
    forallb (fun comp => comp_noninc A comp a a') comps.

  Definition fscc_edge_ok (comps : list (lexcomp A)) (rg : A -> bool)
      (a a' : A) : bool :=
    lex_edge_ok A comps a a'
    || (rg a && rg a' && lex_noninc_all comps a a').

  Definition rgate_ok (Sl : list A) (q : St) (rg : A -> bool) : bool :=
    forallb (fun a =>
      implb (rg a) (negb (st_eqb (a_state a) q)
                    && node_moves_right a && node_rfuel_ge1 a)) Sl.

  Definition fscc_state_ok (Sl : list A) (q : St)
      (comps : list (lexcomp A)) (rg : A -> bool) : bool :=
    rgate_ok Sl q rg &&
    forallb (fun a =>
      if st_eqb (a_state a) q then true
      else match succs a with
           | Some l => forallb (fun a' =>
                         st_eqb (a_state a') q
                         || fscc_edge_ok comps rg a a') l
           | None => false
           end) Sl.

  Definition closure_check_neverqh_fuelscc (t fuel : nat) (a0 : A)
      (cert : St -> list (lexcomp A) * (A -> bool)) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            closed_b A a_enc succs Sl && mem A a_enc a0 Sl &&
            forallb (fun q =>
              implb (cvisits tm c0 t q
                     || existsb (fun a => st_eqb (a_state a) q) Sl)
                    (fscc_state_ok Sl q (fst (cert q)) (snd (cert q))))
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
  Hypothesis node_rfuel_ge1_sound : forall a c,
    node_rfuel_ge1 a = true -> covers a c -> has_right_nonblank (snd c).

  (** A non-increasing component's tracked value does not grow across
      a covered edge (the inline block of [lex_edge_decrease], as a
      standalone fact). *)
  Lemma comp_noninc_eval : forall comp a cc a' cc' l,
    comp_exact tm A succs covers comp ->
    covers a (lift cc) -> covers a' (lift cc') ->
    cstep tm cc = Some cc' ->
    succs a = Some l -> In a' l ->
    comp_noninc A comp a a' = true ->
    comp_eval A comp a' cc' <= comp_eval A comp a cc.
  Proof.
    intros comp a cc a' cc' l Hexact Hca Hca' Hstep Es HInl Hni.
    destruct comp as [phi | mval md K phi gate]; simpl in Hni |- *.
    - apply Nat.leb_le in Hni. exact Hni.
    - apply orb_prop in Hni as [Hng | Hni].
      + rewrite negb_true_iff in Hng. rewrite Hng. lia.
      + apply andb_prop in Hni as [Hg Hz].
        apply andb_prop in Hg as [Hga Hga'].
        rewrite Hga, Hga'.
        apply Z.leb_le in Hz.
        pose proof (Hexact a cc a' cc' l Hca Hca' Hstep Es HInl) as Hd.
        lia.
  Qed.

  (** All components non-increasing: the tuple does not lex-increase. *)
  Lemma tuple_noninc_lexle : forall comps a cc a' cc' l,
    Forall (comp_exact tm A succs covers) comps ->
    covers a (lift cc) -> covers a' (lift cc') ->
    cstep tm cc = Some cc' ->
    succs a = Some l -> In a' l ->
    lex_noninc_all comps a a' = true ->
    lexle (lex_tuple A comps a' cc') (lex_tuple A comps a cc).
  Proof.
    induction comps as [|comp rest IH];
      intros a cc a' cc' l Hex Hca Hca' Hstep Es HInl Hni.
    - right. reflexivity.
    - inversion Hex as [|? ? Hex1 Hexr]; subst.
      simpl in Hni. apply andb_prop in Hni as [Hn1 Hnr].
      assert (Hle1 : comp_eval A comp a' cc' <= comp_eval A comp a cc)
        by (eapply comp_noninc_eval; eauto).
      assert (Hlen : length (lex_tuple A rest a' cc')
                     = length (lex_tuple A rest a cc)).
      { unfold lex_tuple. rewrite !map_length. reflexivity. }
      destruct (IH a cc a' cc' l Hexr Hca Hca' Hstep Es HInl Hnr)
        as [Hlt | Heq].
      + destruct (Nat.lt_ge_cases (comp_eval A comp a' cc')
                                  (comp_eval A comp a cc)) as [H1 | H1].
        * left. left. split; [exact H1 | exact Hlen].
        * left. right. split; [lia | exact Hlt].
      + destruct (Nat.lt_ge_cases (comp_eval A comp a' cc')
                                  (comp_eval A comp a cc)) as [H1 | H1].
        * left. left. split; [exact H1 | exact Hlen].
        * right. cbn [lex_tuple map].
          unfold lex_tuple in Heq. rewrite Heq.
          f_equal. lia.
  Qed.

  (** [step_right_shrinks] restated on [ExecState]. *)
  Lemma step_shrinks_es : forall c c' R,
    step tm c = Some c' -> steps_right tm c ->
    right_bounded (snd c) R -> right_bounded (snd c') (Nat.pred R).
  Proof.
    intros [q1 tp1] [q2 tp2] R Hst Hsr HR.
    simpl in Hsr.
    eapply step_right_shrinks; eauto.
  Qed.

  (** ** The descent

      Outer induction: accessibility of the lex tuple bound [T0]
      (strict drops = lex-good edges).  Inner induction: the right
      window bound (runner edges shrink it while fuel keeps it
      positive).  [lexle _ T0] threads the non-increase through
      runner stretches so a later lex-good edge still strictly drops
      below [T0]. *)
  Lemma fscc_find : forall Sl q comps rg,
    closed_b A a_enc succs Sl = true ->
    fscc_state_ok Sl q comps rg = true ->
    Forall (comp_exact tm A succs covers) comps ->
    forall T0, Acc lexlt T0 ->
    forall r a cc m R,
    lexle (lex_tuple A comps a cc) T0 ->
    right_bounded (snd (lift cc)) R -> R < r ->
    In a Sl -> covers a (lift cc) ->
    stepn tm m InitES = Some (lift cc) ->
    exists n', m <= n' /\ VisitsAt tm q n'.
  Proof.
    intros Sl q comps rg Hcl Hok Hex.
    apply andb_prop in Hok as [Hgate Hedges].
    intros T0 Hacc.
    induction Hacc as [T0 _ IHT].
    induction r as [|r IHr]; intros a cc m R Hle HR Hr HIn Hcov Hm; [lia|].
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
      destruct (st_eqb (a_state a') q) eqn:Eq'.
      + apply st_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists (lift cc'). split; [assumption|].
        rewrite <- (covers_state a' _ Hcov'). assumption.
      + assert (He : fscc_edge_ok comps rg a a' = true).
        { rewrite forallb_forall in Hedges.
          specialize (Hedges a HIn). rewrite Eq, Es in Hedges.
          rewrite forallb_forall in Hedges.
          specialize (Hedges a' HInl). rewrite Eq' in Hedges.
          simpl in Hedges. exact Hedges. }
        apply orb_prop in He as [Hlex | Hrun].
        * (* lex-good edge: strict drop below T0, fresh window bound *)
          assert (Hlt : lexlt (lex_tuple A comps a' cc')
                              (lex_tuple A comps a cc))
            by (eapply lex_edge_decrease; eauto).
          assert (Hlt0 : lexlt (lex_tuple A comps a' cc') T0)
            by (eapply lexlt_lexle_trans; eassumption).
          destruct (extent_le_steps tm (S m) (lift cc') Hm') as [HR' _].
          destruct (IHT _ Hlt0 (S (S m)) a' cc' (S m) (S m)
                      (lexle_refl _) HR' (Nat.lt_succ_diag_r (S m))
                      HIn' Hcov' Hm') as (n' & Hn' & Hv).
          exists n'. split; [lia | assumption].
        * (* runner-internal edge: window shrinks, tuple non-increases *)
          apply andb_prop in Hrun as [Hg Hni].
          apply andb_prop in Hg as [Hga Hga'].
          assert (Hnode : negb (st_eqb (a_state a) q)
                          && node_moves_right a && node_rfuel_ge1 a = true).
          { unfold rgate_ok in Hgate. rewrite forallb_forall in Hgate.
            specialize (Hgate a HIn). rewrite Hga in Hgate.
            exact Hgate. }
          apply andb_prop in Hnode as [Hnode Hfu].
          apply andb_prop in Hnode as [_ Hmv].
          assert (Hsr : steps_right tm (lift cc))
            by (eapply node_moves_right_sound; eauto).
          assert (Hnb : has_right_nonblank (snd (lift cc)))
            by (eapply node_rfuel_ge1_sound; eauto).
          assert (HR1 : 1 <= R)
            by (eapply has_right_nonblank_window_pos; eauto).
          assert (HR' : right_bounded (snd (lift cc')) (Nat.pred R))
            by (eapply step_shrinks_es; eauto).
          assert (Hle' : lexle (lex_tuple A comps a' cc')
                               (lex_tuple A comps a cc))
            by (eapply tuple_noninc_lexle; eauto).
          destruct (IHr a' cc' (S m) (Nat.pred R)
                      (lexle_trans _ _ _ Hle' Hle) HR'
                      ltac:(lia) HIn' Hcov' Hm') as (n' & Hn' & Hv).
          exists n'. split; [lia | assumption].
  Qed.

  (** ** Soundness of the checker *)

  Theorem closure_check_neverqh_fuelscc_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall (comp_exact tm A succs covers) (fst (cert q))) ->
    closure_check_neverqh_fuelscc t fuel a0 cert = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqh_fuelscc in H.
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
    assert (Hlive : fscc_state_ok Sl q (fst (cert q)) (snd (cert q)) = true).
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
      rewrite Hprem in Hq.
      destruct (fscc_state_ok Sl q (fst (cert q)) (snd (cert q)));
        [reflexivity | discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj
                succs_sound Sl Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (extent_le_steps tm M (lift ccM) HM) as [HRM _].
    destruct (fscc_find Sl q (fst (cert q)) (snd (cert q)) Hcl Hlive
                (Hcert q)
                (lex_tuple A (fst (cert q)) aM ccM)
                (lexlt_wf_len
                   (length (lex_tuple A (fst (cert q)) aM ccM)) _ eq_refl)
                (S M) aM ccM M M (lexle_refl _) HRM
                (Nat.lt_succ_diag_r M) HInM HcovM HM)
      as (n' & Hn' & Hv).
    exists n'. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End FuelSCCEngine.
