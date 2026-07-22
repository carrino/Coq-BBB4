(** * IRules.MetaBlkPfxQH: the quasihalting corollary of the Phase-2
    block IRules model (v3/v5/v6/v7 certificates).

    The dual extraction lemma of
    [MetaBlkPfx.irulesblkpfx_check_neverqh], exactly as
    [MetaQH.irules_check_qh] is the dual of [Meta.irules_check_neverqh]
    (see MetaQH.v's header for the argument): the Phase-2 certificate
    builds the same faithful forward-behavior model -- every
    configuration from the anchor on fires a transition in the cycle's
    fired set [F], and every transition in [F] fires unboundedly often.
    Where [MetaBlkPfx] concludes [NeverQuasiHaltsSt] from "every
    prefix-visited state owns a transition in [F]", this checker takes
    a witness state [qz] that is prefix-visited but owns NO transition
    in [F]: it is silent from the anchor on, so the machine QUASIHALTS.
    The score-window pass (no non-[F] state visited in
    [min B anchor, anchor)) bounds every quiet state's last visit below
    [B], giving the census R_QH tier triple
    [NonHalt /\ QHBound B /\ QuasiHaltsSt].

    The whole Phase-2 engine is reused verbatim (certificate record
    [BIRCertP], rule validation [check_rulesBlkP], sentinel-aware
    prefix-splicing replay [breplayKP], anchor re-simulation,
    denotation shift [bwantp_shift]); only the final property lemma is
    new.  No existing file is touched.

    [Print Assumptions irulesblkpfx_check_qh_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaQH.
Import ListNotations.
Open Scope Z_scope.

(** ** The checker

    Checks 1-3 of [irulesblkpfx_check_neverqh] (rule validation,
    anchor re-simulation, symbolic meta-cycle replay under the inward
    meta map), then instead of the all-states-in-[F] coverage:

    4'. [qz] is visited in the prefix but owns no transition in [F]
        (the quasihalt witness), and
    5'. no state outside [F] is visited in the window
        [min B anchor, anchor)  (the score bound). *)

Definition irulesblkpfx_check_qh (tm : TM) (cert : BIRCertP) (qz : St)
    (B : nat) (cfuel fuel : nat) : bool :=
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
          match csteps tm (cp_anchor cert) c0 with
          | Some (q, (l, h, r)) =>
              st_eqb q (cp_st cert) && sym_eqb h (cp_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TR cert))) &&
              cvisits tm c0 (cp_anchor cert) qz &&
              negb (st_in qz F) &&
              match csteps tm (Nat.min B (cp_anchor cert)) c0 with
              | Some cB =>
                  forallb (fun q' =>
                             implb (cvisits tm cB
                                      (cp_anchor cert - Nat.min B (cp_anchor cert))%nat
                                      q')
                                   (st_in q' F)) all_St
              | None => false
              end
          | None => false
          end
      end
  end.

(** ** Soundness

    The middle conjunct IS [QHBound B tm] (Census/TNF_QH.v defines
    [QHBound B tm := forall q s, QuietAfter tm q s -> S s <= B]); it is
    stated unfolded here so the checker stays in the Checkers layer,
    below the census (same convention as [MetaQH] / [Wrap]). *)

Theorem irulesblkpfx_check_qh_sound : forall tm cert qz B cfuel fuel,
  irulesblkpfx_check_qh tm cert qz B cfuel fuel = true ->
  NonHalt tm /\ (forall q s, QuietAfter tm q s -> (S s <= B)%nat) /\
  QuasiHaltsSt tm.
Proof.
  intros tm cert qz B cfuel fuel H.
  unfold irulesblkpfx_check_qh in H. cbv zeta in H.
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
  destruct (csteps tm (cp_anchor cert) c0) as [[q1 [[l1 h1] r1]]|]
    eqn:Hanch; [|discriminate].
  set (W0 := Nat.min B (cp_anchor cert)) in *.
  destruct (csteps tm W0 c0) as [cB|] eqn:HcB;
    [|rewrite !andb_false_r in Hrest; discriminate].
  apply andb_prop in Hrest as [Hrest Hwin].
  apply andb_prop in Hrest as [Hrest HwitF].
  apply andb_prop in Hrest as [Hrest Hwit].
  apply andb_prop in Hrest as [Hrest HpadR].
  apply andb_prop in Hrest as [Hrest HpadL].
  apply andb_prop in Hrest as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  apply negb_true_iff in HwitF.
  (* the anchor configuration is C(k0) *)
  assert (Hanchor : stepn tm (cp_anchor cert) InitES =
                    Some (bsem tbl (fun _ => cp_k0 cert) (btplp_cfg cert))).
  { rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold bsem, bdcfg, btplp_cfg. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity. }
  (* one meta cycle, at every K >= kmin *)
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
  (* the meta map is inward *)
  assert (Hinw : forall K, cp_kmin cert <= K ->
                 cp_kmin cert <= cp_a cert * K + cp_b cert).
  { intros K HK. nia. }
  (* tiling: every index from the anchor on is inside some cycle *)
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
  (* single-index coverage: every index >= anchor fires a transition in F *)
  assert (Hcover : forall m, (cp_anchor cert <= m)%nat ->
    exists cm, stepn tm m InitES = Some cm /\ In (trans_of cm) F).
  { intros m Hm.
    destruct (Htiles (m + 1 - cp_anchor cert)%nat)
      as (N & K & HN & HK & Hstep & Hcov).
    exact (Hcov m Hm ltac:(lia)). }
  (* every transition in F fires unboundedly often *)
  assert (Hrec : forall t, In t F -> forall B0,
    exists m cm, (B0 <= m)%nat /\ stepn tm m InitES = Some cm /\
                 trans_of cm = t).
  { intros t Hin B0.
    destruct (Htiles B0) as (N & K & HN & HK & Hstep & _).
    destruct (Hcycle K HK) as (n & Hn1 & _ & _ & HX).
    destruct (HX t Hin) as (m' & cm & Hm' & Hcm & Htr).
    exists (N + m')%nat, cm.
    split; [lia|]. split; [|exact Htr].
    rewrite stepn_add, Hstep. exact Hcm. }
  (* a state visited at an index >= anchor owns a transition in F *)
  assert (Hlive : forall q n, (cp_anchor cert <= n)%nat ->
    VisitsAt tm q n -> st_in q F = true).
  { intros q n Hn (c & Hc & Hq).
    destruct (Hcover n Hn) as (cm & Hcm & Hin).
    rewrite Hc in Hcm. injection Hcm as <-.
    exact (st_in_complete q _ F Hin
             (eq_trans (fst_trans_of c) Hq)). }
  (* a state visited inside the score window [W0, anchor) owns a
     transition in F *)
  assert (Hwindow : forall q n, (W0 <= n)%nat -> (n < cp_anchor cert)%nat ->
    VisitsAt tm q n -> st_in q F = true).
  { intros q n Hn1 Hn2 (c & Hc & Hq).
    destruct (stepn_csteps tm n c Hc) as (cc & Hcc & Hlift).
    replace n with (W0 + (n - W0))%nat in Hcc by lia.
    rewrite csteps_add, HcB in Hcc.
    assert (Hfst : fst cc = q).
    { rewrite <- Hq, <- Hlift. reflexivity. }
    assert (Hv : cvisits tm cB (cp_anchor cert - W0) q = true).
    { eapply cvisits_complete; [|exact Hcc|exact Hfst]. lia. }
    rewrite forallb_forall in Hwin.
    specialize (Hwin q (all_St_complete q)).
    rewrite Hv in Hwin. simpl in Hwin.
    destruct (st_in q F); [reflexivity | discriminate]. }
  split; [|split].
  - (* NonHalt: the tiling covers every index *)
    intros n Hn.
    destruct (Htiles n) as (N & K & HN & HK & Hstep & _).
    destruct (stepn_prefix tm n N InitES _ ltac:(lia) Hstep)
      as (cm & Hcm & _).
    rewrite Hcm in Hn. discriminate.
  - (* QHBound B: quiet states are outside F, hence unvisited from
       W0 = min B anchor on; their last visit is < W0 <= B *)
    intros q s [Hvis Hquiet].
    destruct (st_in q F) eqn:HqF.
    + (* a state in F recurs unboundedly -- it is never quiet *)
      exfalso.
      destruct (st_in_sound q F HqF) as (t & Hin & Hfst).
      destruct (Hrec t Hin (S s)) as (m & cm & Hm & Hcm & Htr).
      apply (Hquiet m ltac:(lia)).
      exists cm. split; [exact Hcm|].
      rewrite <- Hfst, <- Htr. reflexivity.
    + (* outside F: not visited at any index >= W0 *)
      assert (Hs : (s < W0)%nat).
      { destruct (Nat.lt_ge_cases s W0) as [|Hge]; [assumption|].
        exfalso.
        destruct (Nat.lt_ge_cases s (cp_anchor cert)) as [Hlt|Hge2].
        - rewrite (Hwindow q s Hge Hlt Hvis) in HqF. discriminate.
        - rewrite (Hlive q s Hge2 Hvis) in HqF. discriminate. }
      unfold W0 in Hs. lia.
  - (* QuasiHaltsSt: qz is visited in the prefix and silent from the
       anchor on *)
    exists qz. split.
    + destruct (cvisits_sound _ _ _ _ Hwit) as (i & ci & Hi & Hs & Hq).
      exists i, (lift ci). split.
      * rewrite <- lift_c0. apply csteps_lift. exact Hs.
      * rewrite <- Hq. reflexivity.
    + exists (cp_anchor cert).
      intros n Hn Hvis.
      rewrite (Hlive qz n Hn Hvis) in HwitF. discriminate.
Qed.

Corollary irulesblkpfx_check_qh_quasihalts : forall tm cert qz B cfuel fuel,
  irulesblkpfx_check_qh tm cert qz B cfuel fuel = true -> QuasiHaltsSt tm.
Proof.
  intros tm cert qz B cfuel fuel H.
  exact (proj2 (proj2 (irulesblkpfx_check_qh_sound tm cert qz B cfuel fuel H))).
Qed.

Corollary irulesblkpfx_check_qh_nonhalt : forall tm cert qz B cfuel fuel,
  irulesblkpfx_check_qh tm cert qz B cfuel fuel = true -> NonHalt tm.
Proof.
  intros tm cert qz B cfuel fuel H.
  exact (proj1 (irulesblkpfx_check_qh_sound tm cert qz B cfuel fuel H)).
Qed.
