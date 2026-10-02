(** * FuelSCCTr: instruction recurrence from lexicographic descent and fuel.

    This is the instruction-target version of FuelSCC.  The same
    class-refined nodes and lexicographic components may be used, but
    every gate is checked on the graph avoiding one instruction.
    FuelSCC's component and runner descent lemmas are reused unchanged. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure ClosureTr.
From BBB4.Checkers Require Import Cycle FuelSCC.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section FuelSCCTrEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_instr : A -> Instr.
  Variable succs : A -> option (list A).
  Variable node_moves_right : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.

  (** ** The checker *)

  Definition rgate_tr_ok (Sl : list A) (q : Instr) (rg : A -> bool) : bool :=
    forallb (fun a =>
      implb (rg a) (negb (instr_eqb (a_instr a) q)
                    && node_moves_right a && node_rfuel_ge1 a)) Sl.

  Definition fscc_instr_ok (Sl : list A) (q : Instr)
      (comps : list (lexcomp A)) (rg : A -> bool) : bool :=
    rgate_tr_ok Sl q rg &&
    forallb (fun a =>
      if instr_eqb (a_instr a) q then true
      else match succs a with
           | Some l => forallb (fun a' =>
                         instr_eqb (a_instr a') q
                         || fscc_edge_ok A comps rg a a') l
           | None => false
           end) Sl.

  Definition closure_check_neverqh_fuelscctr (t fuel : nat) (a0 : A)
      (cert : Instr -> list (lexcomp A) * (A -> bool)) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            closed_b A a_enc succs Sl && mem A a_enc a0 Sl &&
            forallb (fun q =>
              implb (cfires tm c0 t q
                     || existsb (fun a => instr_eqb (a_instr a) q) Sl)
                    (fscc_instr_ok Sl q (fst (cert q)) (snd (cert q))))
                    all_Instr
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
  Hypothesis node_moves_right_sound : forall a c,
    node_moves_right a = true -> covers a c -> steps_right tm c.
  Hypothesis node_rfuel_ge1_sound : forall a c,
    node_rfuel_ge1 a = true -> covers a c -> has_right_nonblank (snd c).

  (** ** The descent

      Outer induction: accessibility of the lex tuple bound [T0]
      (strict drops = lex-good edges).  Inner induction: the right
      window bound (runner edges shrink it while fuel keeps it
      positive).  [lexle _ T0] threads the non-increase through
      runner stretches so a later lex-good edge still strictly drops
      below [T0]. *)
  Lemma fscc_find_tr : forall Sl q comps rg,
    closed_b A a_enc succs Sl = true ->
    fscc_instr_ok Sl q comps rg = true ->
    Forall (comp_exact tm A succs covers) comps ->
    forall T0, Acc lexlt T0 ->
    forall r a cc m R,
    lexle (lex_tuple A comps a cc) T0 ->
    right_bounded (snd (lift cc)) R -> R < r ->
    In a Sl -> covers a (lift cc) ->
    stepn tm m InitES = Some (lift cc) ->
    exists n', m <= n' /\ FiresAt tm q n'.
  Proof.
    intros Sl q comps rg Hcl Hok Hex.
    apply andb_prop in Hok as [Hgate Hedges].
    intros T0 Hacc.
    induction Hacc as [T0 _ IHT].
    induction r as [|r IHr]; intros a cc m R Hle HR Hr HIn Hcov Hm; [lia|].
    destruct (instr_eqb (a_instr a) q) eqn:Eq.
    - (* The covered node itself fires the target instruction. *)
      apply instr_eqb_spec in Eq.
      exists m. split; [lia|].
      exists (lift cc). split; [assumption|].
      rewrite <- (covers_instr a (lift cc) Hcov). assumption.
    - destruct (closed_step tm A a_enc succs covers a_enc_inj succs_sound
                  Sl a (lift cc) Hcl HIn Hcov)
        as (c' & l & a' & Hstep & Es & HInl & HIn' & Hcov').
      destruct (cstep_lift_rev tm cc c' Hstep) as (cc' & Hcc' & Hlift).
      subst c'.
      assert (Hm' : stepn tm (S m) InitES = Some (lift cc')).
      { replace (S m) with (m + 1) by lia.
        rewrite stepn_add, Hm. cbn [stepn]. rewrite Hstep. reflexivity. }
      destruct (instr_eqb (a_instr a') q) eqn:Eq'.
      + apply instr_eqb_spec in Eq'.
        exists (S m). split; [lia|].
        exists (lift cc'). split; [assumption|].
        rewrite <- (covers_instr a' _ Hcov'). assumption.
      + assert (He : fscc_edge_ok A comps rg a a' = true).
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
          assert (Hnode : negb (instr_eqb (a_instr a) q)
                          && node_moves_right a && node_rfuel_ge1 a = true).
          { unfold rgate_tr_ok in Hgate. rewrite forallb_forall in Hgate.
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

  Theorem closure_check_neverqh_fuelscctr_sound : forall t fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall (comp_exact tm A succs covers) (fst (cert q))) ->
    closure_check_neverqh_fuelscctr t fuel a0 cert = true ->
    NeverQuasiHaltsTr tm.
  Proof.
    intros t fuel a0 cert Hstart Hcert H.
    unfold closure_check_neverqh_fuelscctr in H.
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
    assert (Hlive : fscc_instr_ok Sl q (fst (cert q)) (snd (cert q)) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_Instr_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cfires tm c0 t q
                      || existsb (fun a => instr_eqb (a_instr a) q) Sl = true).
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
          apply instr_eqb_spec. rewrite (covers_instr a' c' Hcov'). assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cfires_complete; [exact Hlt | exact Hcn' |].
          rewrite <- cinstr_lift. exact Hqn. }
      rewrite Hprem in Hq.
      destruct (fscc_instr_ok Sl q (fst (cert q)) (snd (cert q)));
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
    destruct (fscc_find_tr Sl q (fst (cert q)) (snd (cert q)) Hcl Hlive
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

End FuelSCCTrEngine.
