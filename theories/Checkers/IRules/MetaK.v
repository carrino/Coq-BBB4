(** * IRules.MetaK: the multi-decrement certificate checker.

    A fork of [IRules.Meta.irules_check_neverqh] whose meta-cycle
    replay uses the general step-size applier ([RulesK.replayK] /
    [ruleK_apply]) in place of the v1 single -1 decrement applier
    ([Rules.replay] / [rule_apply]).  Everything else is reused from
    [Meta] unchanged:

    - the certificate record [IRCert] and its templates
      ([tpl_cfg]/[want_cfg]) and the one-cycle denotation shift
      ([want_shift]);
    - the anchor re-simulation and the state-coverage check.

    Rule VALIDATION uses [RulesK.check_rulesK], NOT [Meta.check_rules]:
    a decrement certificate MAY carry rule-in-rule dependencies (a
    later rule's proof applies an already-validated earlier rule -- BBB
    docs/irules2.md "Rule-in-rule application"), which the v1
    [Meta.check_rules] (rules = []) cannot replay.  The meta replay and
    both validations run the general step-size applier ([replayK] /
    [ruleK_apply]).  With a single -1 decrement and no dependency
    [replayK] reduces to [Rules.replay] and this checker to
    [Meta.irules_check_neverqh].

    [Print Assumptions irulesk_check_neverqh_sound] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK AnchorVisits.
Import ListNotations.
Open Scope Z_scope.

(** ** The checker (meta replay via [replayK]) *)

Definition irulesk_check_neverqh (tm : TM) (cert : IRCert) (fuel : nat)
  : bool :=
  (0 <=? c_kmin cert) && (c_kmin cert <=? c_k0 cert) &&
  (0 <=? c_a cert) &&
  (c_kmin cert <=? c_a cert * c_kmin cert + c_b cert) &&
  match check_rulesK tm fuel (c_rules cert) with
  | None => false
  | Some rules =>
      match replayK tm [c_kmin cert] rules
              (fun c => scfg_eqb c (want_cfg cert))
              fuel false (tpl_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps_vis tm (c_anchor cert) c0 vm_empty with
          | Some (q, (l, h, r), vis) =>
              st_eqb q (c_st cert) && sym_eqb h (c_hs cert) &&
              lpad_eqb l (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TL cert))) &&
              lpad_eqb r (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TR cert))) &&
              forallb (fun q' =>
                         implb (vm_get vis q')
                               (st_in q' F)) all_St
          | None => false
          end
      end
  end.

(** ** Soundness (mirrors [Meta.irules_check_neverqh_sound]) *)

Theorem irulesk_check_neverqh_sound : forall tm cert fuel,
  irulesk_check_neverqh tm cert fuel = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm cert fuel H.
  unfold irulesk_check_neverqh in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hinward].
  apply andb_prop in H as [H Ha0].
  apply andb_prop in H as [Hk0 Hkk].
  apply Z.leb_le in Hk0, Hkk, Ha0, Hinward.
  destruct (check_rulesK tm fuel (c_rules cert)) as [rules|] eqn:Hcr;
    [|discriminate].
  destruct (replayK tm [c_kmin cert] rules
              (fun c => scfg_eqb c (want_cfg cert))
              fuel false (tpl_cfg cert)) as [[cend F]|] eqn:Hrep;
    [|discriminate].
  destruct (csteps_vis tm (c_anchor cert) c0 vm_empty)
    as [[[q1 [[l1 h1] r1]] vis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_vis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
  apply andb_prop in Hrest as [Hrest Hpre].
  apply andb_prop in Hrest as [Hrest HpadR].
  apply andb_prop in Hrest as [Hrest HpadL].
  apply andb_prop in Hrest as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  (* the anchor configuration is C(k0) *)
  assert (Hanchor : stepn tm (c_anchor cert) InitES =
                    Some (asem (fun _ => c_k0 cert) (tpl_cfg cert))).
  { rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold asem, dcfg, tpl_cfg. cbn [s_st s_hs s_L s_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity. }
  (* one meta cycle, at every K >= kmin *)
  assert (Hcycle : forall K, c_kmin cert <= K ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (asem (fun _ => K) (tpl_cfg cert))
                   (asem (fun _ => c_a cert * K + c_b cert)
                         (tpl_cfg cert))).
  { intros K HK.
    assert (Hb : bge [c_kmin cert] (fun _ => K))
      by (apply bge_kmin; lia).
    destruct (replayK_sound tm [c_kmin cert] rules _ fuel false
                (tpl_cfg cert) cend F Hrep (fun _ => K) Hb)
      as (Hend & n & HR & Hpos).
    { intros r Fr c1 c2 Hin Happ.
      exact (ruleK_apply_sound tm [c_kmin cert] r Fr c1 c2 Happ
               (check_rulesK_sound tm fuel _ _ Hcr r Fr Hin)
               (fun _ => K) Hb). }
    exists n. split; [apply Hpos; reflexivity|].
    setoid_rewrite (scfg_eqb_asem cend (want_cfg cert)
                      (fun _ => K) Hend) in HR.
    setoid_rewrite (want_shift cert K) in HR.
    exact HR. }
  (* the meta map is inward *)
  assert (Hinw : forall K, c_kmin cert <= K ->
                 c_kmin cert <= c_a cert * K + c_b cert).
  { intros K HK. nia. }
  (* tiling: every index from the anchor on is inside some cycle *)
  assert (Htiles : forall i, exists N K,
    (c_anchor cert + i <= N)%nat /\ c_kmin cert <= K /\
    stepn tm N InitES = Some (asem (fun _ => K) (tpl_cfg cert)) /\
    forall m, (c_anchor cert <= m)%nat -> (m < N)%nat ->
      exists cm, stepn tm m InitES = Some cm /\ In (trans_of cm) F).
  { induction i as [|i IH].
    - exists (c_anchor cert), (c_k0 cert).
      split; [lia|]. split; [lia|]. split; [exact Hanchor|].
      intros m Hm1 Hm2. lia.
    - destruct IH as (N & K & HN & HK & Hstep & Hcov).
      destruct (Hcycle K HK) as (n & Hn1 & HS & HC & _).
      exists (N + n)%nat, (c_a cert * K + c_b cert).
      split; [lia|]. split; [apply Hinw; exact HK|]. split.
      + rewrite stepn_add, Hstep. exact HS.
      + intros m Hm1 Hm2.
        destruct (Nat.lt_ge_cases m N) as [Hlt | Hge].
        * exact (Hcov m Hm1 Hlt).
        * destruct (HC (m - N)%nat ltac:(lia)) as (cm & Hcm & Hin).
          exists cm. split; [|exact Hin].
          replace m with (N + (m - N))%nat by lia.
          rewrite stepn_add, Hstep. exact Hcm. }
  (* every transition in F fires unboundedly often *)
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
  (* the never-quasihalting argument *)
  intros q Hvq B.
  assert (Hqt : exists t, In t F /\ fst t = q).
  { destruct Hvq as (n0 & cn & Hcn & Hqn).
    destruct (Nat.lt_ge_cases n0 (c_anchor cert)) as [Hlt | Hge].
    - destruct (stepn_csteps tm n0 cn Hcn) as (ccn & Hccn & Hlift).
      assert (Hfst : fst ccn = q).
      { destruct ccn as [qq tt]. simpl.
        rewrite <- Hlift in Hqn. exact Hqn. }
      assert (Hv : cvisits tm c0 (c_anchor cert) q = true)
        by (eapply cvisits_complete; eauto).
      assert (Hvm : vm_get vis q = true)
        by (eapply cvisits_csteps_vis; eauto).
      rewrite forallb_forall in Hpre.
      specialize (Hpre q (all_St_complete q)).
      rewrite Hvm in Hpre. simpl in Hpre.
      apply st_in_sound. destruct (st_in q F); [reflexivity|].
      discriminate.
    - destruct (Htiles (n0 + 1 - c_anchor cert)%nat)
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

Corollary irulesk_check_nonhalt : forall tm cert fuel,
  irulesk_check_neverqh tm cert fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_nonhalt, irulesk_check_neverqh_sound; eauto.
Qed.
