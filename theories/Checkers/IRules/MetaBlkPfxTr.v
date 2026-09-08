(** * IRules.MetaBlkPfxTr: the Phase-2 block certificate checker at
    TRANSITION level.

    [MetaBlkPfx.irulesblkpfx_check_neverqh] with the instruction-mask
    prefix gate of [MetaTr]: the scalar meta layer, the sentinel-aware
    block rules ([RulesBlkPfx] / [EngineKS]) and the [a*K + b] cycle
    are reused verbatim; only the anchor prefix gate changes -- every
    instruction FIRED in the walked prefix ([AnchorVisitsTr.csteps_tvis])
    must be in the cycle's recurring fired set [F] -- and the
    conclusion is [NeverQuasiHaltsTr].  Exactly [Meta -> MetaTr]
    (SCOPING_INSTR.md 7.2), applied to the v3/v5/v6/v7 certificate
    format the harness's irules searcher emits for the counters
    (7.1s): the user's 500-machine LIVE sample produced 158 such
    certificates and not one v1.

    [Print Assumptions irulesblkpfx_check_neverqhtr_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx.
Import ListNotations.
Open Scope Z_scope.

From BBB4.Checkers.IRules Require Import MetaBlkPfx.

(** ** The checker *)

Definition irulesblkpfx_check_neverqhtr (tm : TM) (cert : BIRCertP)
    (cfuel fuel : nat) : bool :=
  let blks := cp_blks cert in
  let tbl := mk_tbl blks in
  (0 <=? cp_kmin cert) && (cp_kmin cert <=? cp_k0 cert) &&
  (0 <=? cp_a cert) &&
  (cp_kmin cert <=? cp_a cert * cp_kmin cert + cp_b cert) &&
  match check_rulesBlkP tm tbl blks cfuel fuel (cp_rules cert) with
  | None => false
  | Some rules =>
      match breplayKP tm tbl blks [cp_kmin cert] cfuel rules
              (fun c => bend_eqb tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps_tvis tm (cp_anchor cert) c0 tvm_empty with
          | Some (q, (l, h, r), tvis) =>
              st_eqb q (cp_st cert) && sym_eqb h (cp_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TR cert))) &&
              forallb (fun t =>
                         implb (tvm_get tvis t)
                               (tr_in t F)) all_Instr
          | None => false
          end
      end
  end.

Theorem irulesblkpfx_check_neverqhtr_sound : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqhtr tm cert cfuel fuel = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkpfx_check_neverqhtr in H. cbv zeta in H.
  set (blks := cp_blks cert) in *.
  set (tbl := mk_tbl blks) in *.
  pose proof (mk_tbl_raw blks) as Hraw.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hinward].
  apply andb_prop in H as [H Ha0].
  apply andb_prop in H as [Hk0 Hkk].
  apply Z.leb_le in Hk0, Hkk, Ha0, Hinward.
  destruct (check_rulesBlkP tm tbl blks cfuel fuel (cp_rules cert))
    as [rules|] eqn:Hcr; [|discriminate].
  destruct (breplayKP tm tbl blks [cp_kmin cert] cfuel rules
              (fun c => bend_eqb tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert)) as [[cend F]|]
    eqn:Hrep; [|discriminate].
  destruct (csteps_tvis tm (cp_anchor cert) c0 tvm_empty)
    as [[[q1 [[l1 h1] r1]] tvis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_tvis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
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
    destruct (breplayKP_sound tm tbl blks [cp_kmin cert] cfuel rules _
                (false, false) fuel false
                (btplp_cfg cert) cend F Hraw Hrep (fun _ => K) [] [] Hb
                (fun _ => eq_refl) (fun _ => eq_refl))
      as (Hend & n & HR & Hpos).
    { intros r Fr c1 c2 Hin Happ.
      exact (ruleBlkPfx_apply_sound tm tbl [cp_kmin cert] r Fr c1 c2
               (false, false) Hraw Happ
               (check_rulesBlkP_sound tm tbl blks cfuel fuel _ _ Hraw Hcr
                  r Fr Hin)
               (fun _ => K) Hb [] [] (fun _ => eq_refl) (fun _ => eq_refl)). }
    exists n. split; [apply Hpos; reflexivity|].
    rewrite !bsemX_nil in HR.
    setoid_rewrite (bend_eqb_bsem tbl [cp_kmin cert] cend (bwantp_cfg cert)
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
  (* the transition-level never-quasihalting argument *)
  intros t0 Hf B.
  (* a fired instruction is in the cycle's fired set *)
  assert (Ht0 : In t0 F).
  { destruct Hf as (n0 & cn & Hcn & Htc).
    destruct (Nat.lt_ge_cases n0 (cp_anchor cert)) as [Hlt | Hge].
    - (* prefix: the instruction-mask gate *)
      destruct (stepn_csteps tm n0 cn Hcn) as (ccn & Hccn & Hlift).
      assert (Hm : tvm_get tvis (cinstr ccn) = true)
        by (eapply csteps_tvis_complete; eauto).
      rewrite <- cinstr_lift, Hlift, Htc in Hm.
      rewrite forallb_forall in Hpre.
      specialize (Hpre t0 (all_Instr_complete t0)).
      rewrite Hm in Hpre. simpl in Hpre.
      apply tr_in_sound. destruct (tr_in t0 F); [reflexivity|].
      discriminate.
    - (* from the anchor on: covered by the cycles *)
      destruct (Htiles (n0 + 1 - cp_anchor cert)%nat)
        as (N & K & HN & HK & Hstep & Hcov).
      destruct (Hcov n0 Hge ltac:(lia)) as (cm & Hcm & Hin).
      rewrite Hcn in Hcm. injection Hcm as <-.
      rewrite trans_of_instr_of, Htc in Hin. exact Hin. }
  destruct (Hrec t0 Ht0 B) as (m & cm & Hm & Hcm & Htr).
  exists m. split; [exact Hm|].
  exists cm. split; [exact Hcm|].
  rewrite <- trans_of_instr_of. exact Htr.
Qed.

Corollary irulesblkpfx_check_neverqhtr_nonhalt : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqhtr tm cert cfuel fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_tr_nonhalt, irulesblkpfx_check_neverqhtr_sound; eauto.
Qed.
