(** * IRules.MetaBlkPfxV5b: the Phase-2 block checker with the v5
    end-match AND the gap-2 cell re-blocking.

    A fork of [MetaBlkPfxV5.irulesblkpfx_check_neverqh_v5] whose replay
    ([breplayRB]) additionally applies the denotation-preserving
    re-block [Reblock.breblock_cfg] after every engine step, in BOTH
    rule validation and the meta-cycle replay.  This closes the second
    v5-gap corner (the machines whose rule validation / meta replay
    stalls at a variable-block boundary because the config's near-head
    cells were never re-encoded into the block a certificate rule
    expects; the C verifier's [iv_reblock_side] does this).

    [breblock_cfg] is denotation-preserving ([breblock_cfg_bsemX], via
    [bstreams_eq]), so [breplayRB_sound] is [breplayKP_sound] verbatim
    with one extra rewrite at the engine-step branch, and the whole
    soundness chain (rule validation, the meta cycle, the tiling
    argument) is unchanged.

    [Print Assumptions irulesblkpfx_check_neverqh_v5b_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock.
Import ListNotations.
Open Scope Z_scope.

(** ** The re-blocking replay (fork of [breplayKP]) *)

Fixpoint breplayRB (tm : TM) (tbl : BTbl) (blks : list (nat * list Sym))
    (lo : list Z) (cfuel : nat) (rules : list (BRuleP * list Tr))
    (endt : BCfg -> bool) (sent : bool * bool) (fuel : nat)
    (stepped : bool) (c : BCfg) : option (BCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rulesBlkP lo sent rules c with
        | Some (c', F) =>
            match breplayRB tm tbl blks lo cfuel rules endt sent fuel'
                    stepped c' with
            | Some (cend, F') => Some (cend, tr_union F F')
            | None => None
            end
        | None =>
            match beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c with
            | Some (c', F) =>
                match breplayRB tm tbl blks lo cfuel rules endt sent fuel'
                        true (breblock_cfg lo tbl blks (bcanon lo tbl blks c')) with
                | Some (cend, F') => Some (cend, tr_union F F')
                | None => None
                end
            | None => None
            end
        end
  end.

Lemma breplayRB_sound : forall tm tbl blks lo cfuel rules endt sent fuel
                               stepped c cend F,
  raw_ok tbl ->
  breplayRB tm tbl blks lo cfuel rules endt sent fuel stepped c
    = Some (cend, F) ->
  forall nu XL XR, bge lo nu ->
  (fst sent = false -> XL = []) -> (snd sent = false -> XR = []) ->
  (forall r Fr c1 c2, In (r, Fr) rules ->
     ruleBlkPfx_apply lo sent r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\
       Reach tm Fr n (bsemX tbl nu c1 XL XR) (bsemX tbl nu c2 XL XR)) ->
  endt cend = true /\
  exists n, Reach tm F n (bsemX tbl nu c XL XR) (bsemX tbl nu cend XL XR) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm tbl blks lo cfuel rules endt sent fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F Hraw H nu XL XR Hb
    HXL HXR Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rulesBlkP lo sent rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (breplayRB tm tbl blks lo cfuel rules endt sent fuel
                  stepped c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped c' cend' F' Hraw Hrec nu XL XR Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     ruleBlkPfx_apply lo sent r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (ruleBlkPfx_apply lo sent r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fr ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c)
        as [[c' Fe]|] eqn:Hstep; [|discriminate].
      destruct (breplayRB tm tbl blks lo cfuel rules endt sent fuel true
                  (breblock_cfg lo tbl blks (bcanon lo tbl blks c')))
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true (breblock_cfg lo tbl blks (bcanon lo tbl blks c'))
                  cend' F' Hraw Hrec nu XL XR Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      destruct (beng_stepS_sound tm tbl blks lo (fst sent) (snd sent) cfuel
                  c c' Fe Hraw Hstep nu XL XR Hb HXL HXR)
        as (n1 & Hn1 & HR1).
      rewrite <- (bcanon_bsemX lo tbl blks c' nu XL XR Hraw Hb) in HR1.
      rewrite <- (breblock_cfg_bsemX lo tbl blks (bcanon lo tbl blks c')
                    nu XL XR Hraw Hb) in HR1.
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fe ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

(** ** Rule validation with the re-blocking replay *)

Definition bruleRB_check (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (prior : list (BRuleP * list Tr)) (r : BRuleP) : option (list Tr) :=
  match breplayRB tm tbl blks (brule_lbsP r) cfuel prior
          (fun c => bscfg_eqb c (brulep_end_cfg r)) (brp_pfx r)
          fuel false (brulep_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

Lemma bruleRB_check_sound : forall tm tbl blks cfuel fuel prior r F,
  raw_ok tbl ->
  (forall r' F', In (r', F') prior -> brule_semP tm tbl r' F') ->
  bruleRB_check tm tbl blks cfuel fuel prior r = Some F ->
  brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel prior r F Hraw Hprior H u Hu YL YR HYL HYR.
  unfold bruleRB_check in H.
  destruct (breplayRB tm tbl blks (brule_lbsP r) cfuel prior
              (fun c => bscfg_eqb c (brulep_end_cfg r)) (brp_pfx r)
              fuel false (brulep_start_cfg r)) as [[cend F']|] eqn:Hrep;
    [|discriminate].
  injection H as <-.
  destruct (breplayRB_sound tm tbl blks (brule_lbsP r) cfuel prior _
              (brp_pfx r) fuel false
              (brulep_start_cfg r) cend F' Hraw Hrep u YL YR Hu HYL HYR
              (fun r0 Fr c1 c2 Hin Happ =>
                 ruleBlkPfx_apply_sound tm tbl (brule_lbsP r) r0 Fr c1 c2
                   (brp_pfx r) Hraw Happ (Hprior r0 Fr Hin) u Hu YL YR
                   HYL HYR))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (bscfg_eqb_bsemX tbl cend (brulep_end_cfg r) u YL YR Hend).
  exact HR.
Qed.

Fixpoint check_rulesRB_aux (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (acc : list (BRuleP * list Tr)) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  match rules with
  | [] => Some acc
  | r :: rest =>
      match bruleRB_check tm tbl blks cfuel fuel acc r with
      | Some F =>
          check_rulesRB_aux tm tbl blks cfuel fuel (acc ++ [(r, F)]) rest
      | None => None
      end
  end.

Definition check_rulesRB (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  check_rulesRB_aux tm tbl blks cfuel fuel [] rules.

Lemma check_rulesRB_aux_sound : forall tm tbl blks cfuel fuel rules acc
                                       vrules,
  raw_ok tbl ->
  check_rulesRB_aux tm tbl blks cfuel fuel acc rules = Some vrules ->
  (forall r F, In (r, F) acc -> brule_semP tm tbl r F) ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules. induction rules as [|r0 rest IH];
    intros acc vrules Hraw H Hacc; simpl in H.
  - injection H as <-. exact Hacc.
  - destruct (bruleRB_check tm tbl blks cfuel fuel acc r0) as [F0|] eqn:Hc;
      [|discriminate].
    apply (IH (acc ++ [(r0, F0)]) vrules Hraw H).
    intros r F Hin. apply in_app_or in Hin as [Hin | Hin].
    + apply Hacc; exact Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-.
      exact (bruleRB_check_sound tm tbl blks cfuel fuel acc r0 F0 Hraw
               Hacc Hc).
Qed.

Theorem check_rulesRB_sound : forall tm tbl blks cfuel fuel rules vrules,
  raw_ok tbl ->
  check_rulesRB tm tbl blks cfuel fuel rules = Some vrules ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules vrules Hraw H.
  apply (check_rulesRB_aux_sound tm tbl blks cfuel fuel rules [] vrules
           Hraw H).
  intros r F [].
Qed.

(** ** The checker *)

Definition irulesblkpfx_check_neverqh_v5b (tm : TM) (cert : BIRCertP)
    (cfuel fuel : nat) : bool :=
  let blks := cp_blks cert in
  let tbl := mk_tbl blks in
  (0 <=? cp_kmin cert) && (cp_kmin cert <=? cp_k0 cert) &&
  (0 <=? cp_a cert) &&
  (cp_kmin cert <=? cp_a cert * cp_kmin cert + cp_b cert) &&
  match check_rulesRB tm tbl blks cfuel fuel (cp_rules cert) with
  | None => false
  | Some rules =>
      match breplayRB tm tbl blks [cp_kmin cert] cfuel rules
              (fun c => bend_eqb2 tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps_vis tm (cp_anchor cert) c0 vm_empty with
          | Some (q, (l, h, r), vis) =>
              st_eqb q (cp_st cert) && sym_eqb h (cp_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TR cert))) &&
              forallb (fun q' =>
                         implb (vm_get vis q')
                               (st_in q' F)) all_St
          | None => false
          end
      end
  end.

Theorem irulesblkpfx_check_neverqh_v5b_sound : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqh_v5b tm cert cfuel fuel = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkpfx_check_neverqh_v5b in H. cbv zeta in H.
  set (blks := cp_blks cert) in *.
  set (tbl := mk_tbl blks) in *.
  pose proof (mk_tbl_raw blks) as Hraw.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hinward].
  apply andb_prop in H as [H Ha0].
  apply andb_prop in H as [Hk0 Hkk].
  apply Z.leb_le in Hk0, Hkk, Ha0, Hinward.
  destruct (check_rulesRB tm tbl blks cfuel fuel (cp_rules cert))
    as [rules|] eqn:Hcr; [|discriminate].
  destruct (breplayRB tm tbl blks [cp_kmin cert] cfuel rules
              (fun c => bend_eqb2 tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert)) as [[cend F]|]
    eqn:Hrep; [|discriminate].
  destruct (csteps_vis tm (cp_anchor cert) c0 vm_empty)
    as [[[q1 [[l1 h1] r1]] vis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_vis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
  apply andb_prop in Hrest as [Hrest Hpre].
  apply andb_prop in Hrest as [Hrest HpadR].
  apply andb_prop in Hrest as [Hrest HpadL].
  apply andb_prop in Hrest as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  assert (Hanchor : stepn tm (cp_anchor cert) InitES =
                    Some (bsem tbl (fun _ => cp_k0 cert) (btplp_cfg cert))).
  { rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold bsem, bdcfg, btplp_cfg. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity. }
  assert (Hcycle : forall K, cp_kmin cert <= K ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (bsem tbl (fun _ => K) (btplp_cfg cert))
                   (bsem tbl (fun _ => cp_a cert * K + cp_b cert)
                         (btplp_cfg cert))).
  { intros K HK.
    assert (Hb : bge [cp_kmin cert] (fun _ => K))
      by (apply bge_kmin; lia).
    destruct (breplayRB_sound tm tbl blks [cp_kmin cert] cfuel rules _
                (false, false) fuel false
                (btplp_cfg cert) cend F Hraw Hrep (fun _ => K) [] [] Hb
                (fun _ => eq_refl) (fun _ => eq_refl))
      as (Hend & n & HR & Hpos).
    { intros r Fr c1 c2 Hin Happ.
      exact (ruleBlkPfx_apply_sound tm tbl [cp_kmin cert] r Fr c1 c2
               (false, false) Hraw Happ
               (check_rulesRB_sound tm tbl blks cfuel fuel _ _ Hraw Hcr
                  r Fr Hin)
               (fun _ => K) Hb [] [] (fun _ => eq_refl) (fun _ => eq_refl)). }
    exists n. split; [apply Hpos; reflexivity|].
    rewrite !bsemX_nil in HR.
    setoid_rewrite (bend_eqb2_bsem tbl [cp_kmin cert] cend (bwantp_cfg cert)
                      (fun _ => K) Hraw Hb Hend) in HR.
    setoid_rewrite (bwantp_shift tbl cert K) in HR.
    exact HR. }
  assert (Hinw : forall K, cp_kmin cert <= K ->
                 cp_kmin cert <= cp_a cert * K + cp_b cert).
  { intros K HK. nia. }
  assert (Htiles : forall i, exists N K,
    (cp_anchor cert + i <= N)%nat /\ cp_kmin cert <= K /\
    stepn tm N InitES = Some (bsem tbl (fun _ => K) (btplp_cfg cert)) /\
    forall m, (cp_anchor cert <= m)%nat -> (m < N)%nat ->
      exists cm, stepn tm m InitES = Some cm /\ In (trans_of cm) F).
  { induction i as [|i IH].
    - exists (cp_anchor cert), (cp_k0 cert).
      split; [lia|]. split; [lia|]. split; [exact Hanchor|].
      intros m Hm1 Hm2. lia.
    - destruct IH as (N & K & HN & HK & Hstep & Hcov).
      destruct (Hcycle K HK) as (n & Hn1 & HS & HC & _).
      exists (N + n)%nat, (cp_a cert * K + cp_b cert).
      split; [lia|]. split; [apply Hinw; exact HK|]. split.
      + rewrite stepn_add, Hstep. exact HS.
      + intros m Hm1 Hm2.
        destruct (Nat.lt_ge_cases m N) as [Hlt | Hge].
        * exact (Hcov m Hm1 Hlt).
        * destruct (HC (m - N)%nat ltac:(lia)) as (cm & Hcm & Hin).
          exists cm. split; [|exact Hin].
          replace m with (N + (m - N))%nat by lia.
          rewrite stepn_add, Hstep. exact Hcm. }
  assert (Hrec : forall t, In t F -> forall B,
    exists m cm, (B <= m)%nat /\ stepn tm m InitES = Some cm /\
                 trans_of cm = t).
  { intros t Hin B.
    destruct (Htiles B) as (N & K & HN & HK & Hstep & _).
    destruct (Hcycle K HK) as (n & Hn1 & _ & _ & HX).
    destruct (HX t Hin) as (m' & cm & Hm' & Hcm & Htr).
    exists (N + m')%nat, cm.
    split; [lia|]. split; [|exact Htr].
    rewrite stepn_add, Hstep. exact Hcm. }
  intros q Hvq B.
  assert (Hqt : exists t, In t F /\ fst t = q).
  { destruct Hvq as (n0 & cn & Hcn & Hqn).
    destruct (Nat.lt_ge_cases n0 (cp_anchor cert)) as [Hlt | Hge].
    - destruct (stepn_csteps tm n0 cn Hcn) as (ccn & Hccn & Hlift).
      assert (Hfst : fst ccn = q).
      { destruct ccn as [qq tt]. simpl.
        rewrite <- Hlift in Hqn. exact Hqn. }
      assert (Hv : cvisits tm c0 (cp_anchor cert) q = true)
        by (eapply cvisits_complete; eauto).
      assert (Hvm : vm_get vis q = true)
        by (eapply cvisits_csteps_vis; eauto).
      rewrite forallb_forall in Hpre.
      specialize (Hpre q (all_St_complete q)).
      rewrite Hvm in Hpre. simpl in Hpre.
      apply st_in_sound. destruct (st_in q F); [reflexivity|].
      discriminate.
    - destruct (Htiles (n0 + 1 - cp_anchor cert)%nat)
        as (N & K & HN & HK & Hstep & Hcov).
      destruct (Hcov n0 Hge ltac:(lia)) as (cm & Hcm & Hin).
      rewrite Hcn in Hcm. injection Hcm as <-.
      exists (trans_of cn). split; [exact Hin|].
      unfold trans_of. simpl. exact Hqn. }
  destruct Hqt as (t & Hin & Hfst).
  destruct (Hrec t Hin B) as (m & cm & Hm & Hcm & Htr).
  exists m. split; [exact Hm|].
  exists cm. split; [exact Hcm|].
  rewrite <- Hfst, <- Htr. reflexivity.
Qed.

Corollary irulesblkpfx_check_neverqh_v5b_nonhalt : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqh_v5b tm cert cfuel fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_nonhalt, irulesblkpfx_check_neverqh_v5b_sound; eauto.
Qed.
