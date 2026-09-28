(** * IRules.MetaBlkPfxQHTr: the quasihalting corollary of the Phase-2
    block IRules model at TRANSITION level.

    [MetaBlkPfxQH] is to [MetaBlkPfx] what this file is to
    [MetaBlkPfxTr]: the same certificate builds the same forward model
    -- every configuration from the anchor on fires an instruction in
    the meta cycle's fired set [F], and every instruction in [F] fires
    after every index -- and where [MetaBlkPfxTr] concludes
    [NeverQuasiHaltsTr] from "every instruction fired in the prefix is
    in [F]", this checker takes a witness instruction [tz] that fires in
    the prefix but is NOT in [F]: it is silent from the anchor on, so
    the machine quasihalts at instruction level.

    The score bound needs no window: an instruction outside [F] never
    fires at an index >= anchor, so its last fire is below the anchor,
    and an instruction in [F] is never quiet.  So the bound is the
    anchor itself; [irulesblkpfx_check_qhtr_close] lifts it to the
    closeout's literal [B_close = 32779478] for anchors up to 2^20
    (the harness's anchors are under its 200,000-step budget), with the
    unary comparison built once here rather than once per row.

    Nothing of the engine is new: the rule validation, the replay, the
    anchor re-simulation with the instruction mask ([csteps_tvis]) and
    the denotation shift are [MetaBlkPfxTr]'s, verbatim.

    [Print Assumptions irulesblkpfx_check_qhtr_close] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.

(** ** The checker

    Checks 1-3 of [irulesblkpfx_check_neverqhtr], then in place of the
    all-fired-instructions-in-[F] gate: [tz] fires at index [nz], and
    [tz] is not in [F]. *)

Definition irulesblkpfx_check_qhtr (tm : TM) (cert : BIRCertP) (tz : Tr)
    (nz cfuel fuel : nat) : bool :=
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
          match csteps tm (cp_anchor cert) c0, csteps tm nz c0 with
          | Some (q, (l, h, r)), Some cz =>
              st_eqb q (cp_st cert) && sym_eqb h (cp_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => cp_k0 cert)
                            (btpl_start (cp_TR cert))) &&
              instr_eqb (cinstr cz) tz && negb (tr_in tz F)
          | _, _ => false
          end
      end
  end.

(** ** Soundness, with the bound at the anchor *)

Theorem irulesblkpfx_check_qhtr_sound : forall tm cert tz nz cfuel fuel,
  irulesblkpfx_check_qhtr tm cert tz nz cfuel fuel = true ->
  NonHalt tm /\
  (forall t s, QuietAfterTr tm t s -> (S s <= cp_anchor cert)%nat) /\
  QuasiHaltsTr tm.
Proof.
  intros tm cert tz nz cfuel fuel H.
  unfold irulesblkpfx_check_qhtr in H. cbv zeta in H.
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
  destruct (csteps tm nz c0) as [cz|] eqn:Hcz; [|discriminate].
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
  (* an instruction fired at an index >= anchor is in F *)
  assert (Hlive : forall t n, (cp_anchor cert <= n)%nat ->
    FiresAt tm t n -> In t F).
  { intros t n Hn (c & Hc & Ht).
    destruct (Htiles (n + 1 - cp_anchor cert)%nat)
      as (N & K & HN & HK & Hstep & Hcov).
    destruct (Hcov n Hn ltac:(lia)) as (cm & Hcm & Hin).
    rewrite Hc in Hcm. injection Hcm as <-.
    rewrite trans_of_instr_of, Ht in Hin. exact Hin. }
  (* every instruction in F fires after every index *)
  assert (Hrec : forall t, In t F -> forall B0,
    exists m, (B0 <= m)%nat /\ FiresAt tm t m).
  { intros t Hin B0.
    destruct (Htiles B0) as (N & K & HN & HK & Hstep & _).
    destruct (Hcycle K HK) as (n & Hn1 & _ & _ & HX).
    destruct (HX t Hin) as (m' & cm & Hm' & Hcm & Htr).
    exists (N + m')%nat. split; [lia|].
    exists cm. split.
    - rewrite stepn_add, Hstep. exact Hcm.
    - rewrite <- trans_of_instr_of. exact Htr. }
  assert (HtzF : ~ In tz F).
  { intro Hin. unfold tr_in in HwitF.
    assert (existsb (instr_eqb tz) F = true).
    { apply existsb_exists. exists tz. split; [exact Hin|].
      apply instr_eqb_spec. reflexivity. }
    congruence. }
  split; [|split].
  - (* NonHalt: the tiling covers every index *)
    intros n Hn.
    destruct (Htiles n) as (N & K & HN & HK & Hstep & _).
    destruct (stepn_prefix tm n N InitES _ ltac:(lia) Hstep)
      as (cm & Hcm & _).
    rewrite Hcm in Hn. discriminate.
  - (* the bound: a quiet instruction is outside F, so it last fires
       before the anchor *)
    intros t s [Hfs Hquiet].
    destruct (Nat.lt_ge_cases s (cp_anchor cert)) as [Hlt | Hge]; [lia|].
    exfalso.
    destruct (Hrec t (Hlive t s Hge Hfs) (S s)) as (m & Hm & Hfm).
    exact (Hquiet m ltac:(lia) Hfm).
  - (* QuasiHaltsTr: tz fired in the prefix and is silent from the
       anchor on *)
    exists tz. split.
    + exists nz, (lift cz). split.
      * rewrite <- lift_c0. apply csteps_lift. exact Hcz.
      * rewrite cinstr_lift. apply instr_eqb_spec. exact Hwit.
    + exists (cp_anchor cert).
      intros n Hn Hfn.
      exact (HtzF (Hlive tz n Hn Hfn)).
Qed.

(** ** At the closeout's bound

    [B_close = 32779478]; the unary comparison is made once here. *)

Local Open Scope nat_scope.

Lemma anchor_le_B_close : forall n,
  (n <=? 1048576)%nat = true -> (n <= 32779478)%nat.
Proof.
  intros n H. apply Nat.leb_le in H.
  apply (Nat.le_trans _ _ _ H). apply Nat.leb_le.
  vm_cast_no_check (eq_refl true).
Qed.

Corollary irulesblkpfx_check_qhtr_close : forall tm cert tz nz cfuel fuel,
  irulesblkpfx_check_qhtr tm cert tz nz cfuel fuel = true ->
  (cp_anchor cert <=? 1048576)%nat = true ->
  NonHalt tm /\
  (forall t s, QuietAfterTr tm t s -> (S s <= 32779478)%nat) /\
  QuasiHaltsTr tm.
Proof.
  intros tm cert tz nz cfuel fuel H Ha.
  destruct (irulesblkpfx_check_qhtr_sound tm cert tz nz cfuel fuel H)
    as (Hnh & Hb & Hq).
  split; [exact Hnh|]. split; [|exact Hq].
  intros t s Hts. specialize (Hb t s Hts).
  pose proof (anchor_le_B_close _ Ha). lia.
Qed.
