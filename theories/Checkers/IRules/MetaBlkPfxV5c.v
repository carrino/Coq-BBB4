(** * IRules.MetaBlkPfxV5c: the Phase-2 block checker with the v5b
    re-blocking replay PLUS (c) block-hop closure and the generalised
    multi-run cell-stream end-match.

    A fork of [MetaBlkPfxV5b.irulesblkpfx_check_neverqh_v5b] with exactly
    two changes, both of which leave the soundness chain intact:

    - the block table is CLOSED ([BlkClosure.blk_closure]) before use, so
      the clean crossing [bhop_result] resolves the rotation blocks a
      hop can produce (see BlkClosure.v).  This is untrusted
      preprocessing: every hop is re-verified against [mk_tbl blks], the
      whole chain is parametric in [blks], and [mk_tbl_raw] gives
      [raw_ok] for ANY block list, so the proof is unchanged -- [blks]
      is just a (larger) opaque table.

    - the meta-cycle end-match is [StreamEq2.bend_eqb3] (=
      [bend_eqb2 || cseq2]) instead of [bend_eqb2]; [bend_eqb3_bsem]
      replaces [bend_eqb2_bsem] at the single cycle-closing step.

    Empirically (deep measurement this session, see docs/V5GAP_STAGE.md)
    these two changes are jointly SUFFICIENT AND NECESSARY for the 8
    remaining scalar v5-gap machines: with the closed table the engine
    ([EngineKS.beng_stepS], UNCHANGED) tracks the C verifier's [iv_step]
    byte-for-byte through the whole meta cycle, reaching a configuration
    CELL-equal to the shifted template whose two sides each carry two
    variable-count runs -- which [bend_eqb2]/[cseq] (one pump) refuse
    and [cseq2] (strip common runs, then one pump) accepts.  No engine
    "zipper" is required (the prior hand-off's hypothesis is superseded).

    [Print Assumptions irulesblkpfx_check_neverqh_v5c_sound] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock MetaBlkPfxV5b BlkClosure StreamEq2.
Import ListNotations.
Open Scope Z_scope.

(** Closure fuel: each pass either grows the table or the length-guard
    early-exits, and the measured tables close in one pass (+1 block);
    a generous fixed bound keeps the checker a closed term. *)
Definition v5c_closure_fuel : nat := 16.

Definition irulesblkpfx_check_neverqh_v5c (tm : TM) (cert : BIRCertP)
    (cfuel fuel : nat) : bool :=
  let blks := blk_closure tm (cp_blks cert) v5c_closure_fuel in
  let tbl := mk_tbl blks in
  (0 <=? cp_kmin cert) && (cp_kmin cert <=? cp_k0 cert) &&
  (0 <=? cp_a cert) &&
  (cp_kmin cert <=? cp_a cert * cp_kmin cert + cp_b cert) &&
  match check_rulesRB tm tbl blks cfuel fuel (cp_rules cert) with
  | None => false
  | Some rules =>
      match breplayRB tm tbl blks [cp_kmin cert] cfuel rules
              (fun c => bend_eqb3 tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps tm (cp_anchor cert) c0 with
          | Some (q, (l, h, r)) =>
              st_eqb q (cp_st cert) && sym_eqb h (cp_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TR cert))) &&
              forallb (fun q' =>
                         implb (cvisits tm c0 (cp_anchor cert) q')
                               (st_in q' F)) all_St
          | None => false
          end
      end
  end.

Theorem irulesblkpfx_check_neverqh_v5c_sound : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqh_v5c tm cert cfuel fuel = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkpfx_check_neverqh_v5c in H. cbv zeta in H.
  set (blks := blk_closure tm (cp_blks cert) v5c_closure_fuel) in *.
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
              (fun c => bend_eqb3 tbl [cp_kmin cert] c (bwantp_cfg cert))
              (false, false) fuel false (btplp_cfg cert)) as [[cend F]|]
    eqn:Hrep; [|discriminate].
  destruct (csteps tm (cp_anchor cert) c0) as [[q1 [[l1 h1] r1]]|]
    eqn:Hanch; [|discriminate].
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
    setoid_rewrite (bend_eqb3_bsem tbl [cp_kmin cert] cend (bwantp_cfg cert)
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
      rewrite forallb_forall in Hpre.
      specialize (Hpre q (all_St_complete q)).
      rewrite Hv in Hpre. simpl in Hpre.
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

Corollary irulesblkpfx_check_neverqh_v5c_nonhalt : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqh_v5c tm cert cfuel fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_nonhalt, irulesblkpfx_check_neverqh_v5c_sound; eauto.
Qed.
