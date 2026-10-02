(** * FuelMixTargetTr: extract independently checked instruction recurrence. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure ClosureTr.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramTr Fuel
  FuelClass FuelSCC FuelWide FuelSCCTr FuelWideTr FuelMixTr FuelMixPartialTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section FuelSCCTrTarget.
  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_instr : A -> Instr.
  Variable succs : A -> option (list A).
  Variable node_moves_right : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.

  (** ** Per-instruction soundness *)

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

  Theorem closure_check_neverqh_fuelscctr_target_sound : forall t fuel a0 skip cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall (comp_exact tm A succs covers) (fst (cert q))) ->
    closure_check_neverqh_fuelscctr_except tm A a_enc a_instr succs node_moves_right node_rfuel_ge1 t fuel a0 skip cert = true ->
    forall q, skip q=false -> FiredTr tm q -> forall N, exists j,N<=j /\ FiresAt tm q j.
  Proof.
    intros t fuel a0 skip cert Hstart Hcert H.
    unfold closure_check_neverqh_fuelscctr_except in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0])
      as [Sl|]; [|discriminate].
    apply andb_prop in H as [H Hq].
    apply andb_prop in H as [Hcl Hin].
    apply (mem_In A a_enc a_enc_inj) in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hskip Hvq N.
    assert (Hlive : fscc_instr_ok A a_instr succs node_moves_right node_rfuel_ge1 Sl q (fst (cert q)) (snd (cert q)) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_Instr_complete q)).
      rewrite Hskip in Hq. cbn in Hq.
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
      destruct (fscc_instr_ok A a_instr succs node_moves_right node_rfuel_ge1 Sl q (fst (cert q)) (snd (cert q)));
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
    destruct (fscc_find_tr tm A a_enc a_instr succs node_moves_right node_rfuel_ge1
                covers a_enc_inj covers_instr succs_sound
                node_moves_right_sound node_rfuel_ge1_sound Sl q (fst (cert q)) (snd (cert q)) Hcl Hlive
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

End FuelSCCTrTarget.

Theorem ngram_check_neverqh_fuelmixtr_target_sound : forall tm n t fuel rounds skip cert,
  ngram_check_neverqh_fuelmixtr_except tm n t fuel rounds skip cert = true ->
  forall q, skip q=false -> FiredTr tm q -> forall N, exists j,N<=j /\ FiresAt tm q j.
Proof.
  intros tm n t fuel rounds skip cert H.
  unfold ngram_check_neverqh_fuelmixtr_except in H.
  apply andb_prop in H as [Hn H]. apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  intros target Hskip Hf N.
  eapply (closure_check_neverqh_fuelscctr_target_sound tm fcconf fcconf_enc fw_instr
           (fw_succs tm lset rset)
           (fwnode_moves_right tm) fwnode_rfuel_ge1
           (fw_covers n lset rset)) with
    (cert:=fun q=>fmx_cert_denote tm n(cert q))(a0:=fw_start n(q,(l,h,r)))(t:=t)(fuel:=fuel)(skip:=skip).
  - exact fcconf_enc_inj.
  - intros a c Hc. eapply fw_covers_instr; eauto.
  - intros a c Hc. apply fw_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound; eauto.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply fw_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    cbn [fmx_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply fmx_comp_exact.
  - exact Hcheck.
  - exact Hskip.
  - exact Hf.
Qed.
