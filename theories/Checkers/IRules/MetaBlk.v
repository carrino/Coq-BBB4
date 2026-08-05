(** * IRules.MetaBlk: the block-run certificate checker.

    A fork of [MetaK.irulesk_check_neverqh] whose meta-cycle replay runs
    the block engine ([RulesBlk.breplayK] over [EngineK.beng_step]) and
    whose configurations denote through [EngineK.bdside tbl] for the
    certificate's (untrusted) block table.  Templates, anchor re-sim and
    state coverage mirror [Meta] against [bdside]; the meta-cycle
    end-match falls back from strict run equality to provable cell-stream
    equality ([RulesBlk.bend_eqb]).

    The block table is carried as an association list [c_blks] and read
    back through [mk_tbl] (raw ids 0/1 hardwired to their singleton
    cells, so [raw_ok] holds by construction and the table is never
    trusted).

    [Print Assumptions irulesblk_check_neverqh_sound] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk.
Import ListNotations.
Open Scope Z_scope.

(** ** The block table from an association list *)

Fixpoint assoc_blk (blks : list (nat * list Sym)) (s : nat)
  : option (list Sym) :=
  match blks with
  | [] => None
  | (i, c) :: t => if Nat.eqb i s then Some c else assoc_blk t s
  end.

Definition mk_tbl (blks : list (nat * list Sym)) : BTbl :=
  fun s =>
    match s with
    | O => [S0]
    | S O => [S1]
    | _ => match assoc_blk blks s with Some c => c | None => [] end
    end.

Lemma mk_tbl_raw : forall blks, raw_ok (mk_tbl blks).
Proof. intro blks. split; reflexivity. Qed.

(** ** Templates *)

Definition BTRun : Set := (BSym * Z * Z)%type.

Definition btpl_start (rs : list BTRun) : list BRun :=
  map (fun r => let '(s, al, be) := r in (s, mkExpr be [al])) rs.

Definition btpl_want (a b : Z) (rs : list BTRun) : list BRun :=
  map (fun r => let '(s, al, be) := r in
                (s, mkExpr (al * b + be) [al * a])) rs.

Record BIRCert : Set := mkBIRCert {
  c_anchor : nat;
  c_k0 : Z;
  c_kmin : Z;
  c_a : Z;
  c_b : Z;
  c_st : St;
  c_hs : Sym;
  c_blks : list (nat * list Sym);
  c_TL : list BTRun;
  c_TR : list BTRun;
  c_rules : list BRule
}.

Definition btpl_cfg (cert : BIRCert) : BCfg :=
  mkBCfg (c_st cert) (c_hs cert)
         (btpl_start (c_TL cert)) (btpl_start (c_TR cert)).

Definition bwant_cfg (cert : BIRCert) : BCfg :=
  mkBCfg (c_st cert) (c_hs cert)
         (btpl_want (c_a cert) (c_b cert) (c_TL cert))
         (btpl_want (c_a cert) (c_b cert) (c_TR cert)).

Lemma btpl_shift : forall tbl a b K rs,
  bdside tbl (fun _ => K) (btpl_want a b rs) =
  bdside tbl (fun _ => a * K + b) (btpl_start rs).
Proof.
  induction rs as [|[[s al] be] t IH]; [reflexivity|].
  simpl btpl_want. simpl btpl_start.
  rewrite !bdside_cons, IH.
  f_equal. f_equal.
  unfold cnt. f_equal.
  unfold eval. cbn [dot e_c0 e_cf]. ring.
Qed.

Lemma bwant_shift : forall tbl cert K,
  bsem tbl (fun _ => K) (bwant_cfg cert) =
  bsem tbl (fun _ => c_a cert * K + c_b cert) (btpl_cfg cert).
Proof.
  intros. unfold bsem, bdcfg, bwant_cfg, btpl_cfg.
  cbn [b_st b_hs b_L b_R].
  rewrite !btpl_shift. reflexivity.
Qed.

(** ** The checker *)

Definition irulesblk_check_neverqh (tm : TM) (cert : BIRCert)
    (cfuel fuel : nat) : bool :=
  let blks := c_blks cert in
  let tbl := mk_tbl blks in
  (0 <=? c_kmin cert) && (c_kmin cert <=? c_k0 cert) &&
  (0 <=? c_a cert) &&
  (c_kmin cert <=? c_a cert * c_kmin cert + c_b cert) &&
  match check_rulesBlk tm tbl blks cfuel fuel (c_rules cert) with
  | None => false
  | Some rules =>
      match breplayK tm tbl blks [c_kmin cert] cfuel rules
              (fun c => bend_eqb tbl [c_kmin cert] c (bwant_cfg cert))
              fuel false (btpl_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps_vis tm (c_anchor cert) c0 vm_empty with
          | Some (q, (l, h, r), vis) =>
              st_eqb q (c_st cert) && sym_eqb h (c_hs cert) &&
              lpad_eqb l (bdside tbl (fun _ => c_k0 cert)
                            (btpl_start (c_TL cert))) &&
              lpad_eqb r (bdside tbl (fun _ => c_k0 cert)
                            (btpl_start (c_TR cert))) &&
              forallb (fun q' =>
                         implb (vm_get vis q')
                               (st_in q' F)) all_St
          | None => false
          end
      end
  end.

Theorem irulesblk_check_neverqh_sound : forall tm cert cfuel fuel,
  irulesblk_check_neverqh tm cert cfuel fuel = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblk_check_neverqh in H. cbv zeta in H.
  set (blks := c_blks cert) in *.
  set (tbl := mk_tbl blks) in *.
  pose proof (mk_tbl_raw blks) as Hraw.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hinward].
  apply andb_prop in H as [H Ha0].
  apply andb_prop in H as [Hk0 Hkk].
  apply Z.leb_le in Hk0, Hkk, Ha0, Hinward.
  destruct (check_rulesBlk tm tbl blks cfuel fuel (c_rules cert)) as [rules|]
    eqn:Hcr; [|discriminate].
  destruct (breplayK tm tbl blks [c_kmin cert] cfuel rules
              (fun c => bend_eqb tbl [c_kmin cert] c (bwant_cfg cert))
              fuel false (btpl_cfg cert)) as [[cend F]|] eqn:Hrep;
    [|discriminate].
  destruct (csteps_vis tm (c_anchor cert) c0 vm_empty)
    as [[[q1 [[l1 h1] r1]] vis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_vis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
  apply andb_prop in Hrest as [Hrest Hpre].
  apply andb_prop in Hrest as [Hrest HpadR].
  apply andb_prop in Hrest as [Hrest HpadL].
  apply andb_prop in Hrest as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  assert (Hanchor : stepn tm (c_anchor cert) InitES =
                    Some (bsem tbl (fun _ => c_k0 cert) (btpl_cfg cert))).
  { rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold bsem, bdcfg, btpl_cfg. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity. }
  assert (Hcycle : forall K, c_kmin cert <= K ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (bsem tbl (fun _ => K) (btpl_cfg cert))
                   (bsem tbl (fun _ => c_a cert * K + c_b cert)
                         (btpl_cfg cert))).
  { intros K HK.
    assert (Hb : bge [c_kmin cert] (fun _ => K))
      by (apply bge_kmin; lia).
    destruct (breplayK_sound tm tbl blks [c_kmin cert] cfuel rules _ fuel false
                (btpl_cfg cert) cend F Hraw Hrep (fun _ => K) Hb)
      as (Hend & n & HR & Hpos).
    { intros r Fr c1 c2 Hin Happ.
      exact (ruleBlk_apply_sound tm tbl [c_kmin cert] r Fr c1 c2 Hraw Happ
               (check_rulesBlk_sound tm tbl blks cfuel fuel _ _ Hraw Hcr r Fr Hin)
               (fun _ => K) Hb). }
    exists n. split; [apply Hpos; reflexivity|].
    setoid_rewrite (bend_eqb_bsem tbl [c_kmin cert] cend (bwant_cfg cert)
                      (fun _ => K) Hraw Hb Hend) in HR.
    setoid_rewrite (bwant_shift tbl cert K) in HR.
    exact HR. }
  assert (Hinw : forall K, c_kmin cert <= K ->
                 c_kmin cert <= c_a cert * K + c_b cert).
  { intros K HK. nia. }
  assert (Htiles : forall i, exists N K,
    (c_anchor cert + i <= N)%nat /\ c_kmin cert <= K /\
    stepn tm N InitES = Some (bsem tbl (fun _ => K) (btpl_cfg cert)) /\
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

Corollary irulesblk_check_nonhalt : forall tm cert cfuel fuel,
  irulesblk_check_neverqh tm cert cfuel fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_nonhalt, irulesblk_check_neverqh_sound; eauto.
Qed.
