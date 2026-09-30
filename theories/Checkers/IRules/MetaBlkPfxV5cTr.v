(** * IRules.MetaBlkPfxV5cTr: the v5c block certificate checker at
    TRANSITION level.

    [MetaBlkPfxV5c.irulesblkpfx_check_neverqh_v5c] (the closed block
    table, the re-blocking replay [breplayRB] and the multi-run
    cell-stream end-match [bend_eqb3]) with the instruction-mask prefix
    gate of [MetaBlkPfxTr], concluding [NeverQuasiHaltsTr].  Exactly
    [MetaBlkPfx -> MetaBlkPfxTr], applied to the stronger engine.

    Why: the class-SP irules route (SCOPING_INSTR.md 7.4.SP) ran every
    certificate through [MetaBlkPfxTr] only, and its "false" and
    "timeout" probes are BBB-verified certificates whose meta replay
    stalls at a block boundary the plain engine cannot re-block; on the
    7.4.SPW sample every one of them checks under v5c in 1-2 s.

    The recurrence argument is [MetaTileTr.meta_tile_neverqhtr]; this
    file proves only the anchor and the cycle.

    [Print Assumptions irulesblkpfx_check_neverqhtr_v5c_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock MetaBlkPfxV5b BlkClosure StreamEq2 MetaBlkPfxV5c
     MetaTileTr.
Import ListNotations.
Open Scope Z_scope.

Definition irulesblkpfx_check_neverqhtr_v5c (tm : TM) (cert : BIRCertP)
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

Theorem irulesblkpfx_check_neverqhtr_v5c_sound : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqhtr_v5c tm cert cfuel fuel = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkpfx_check_neverqhtr_v5c in H. cbv zeta in H.
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
  destruct (csteps_tvis tm (cp_anchor cert) c0 tvm_empty)
    as [[[q1 [[l1 h1] r1]] tvis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_tvis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
  apply andb_prop in Hrest as [Hrest Hpre].
  apply andb_prop in Hrest as [Hrest HpadR].
  apply andb_prop in Hrest as [Hrest HpadL].
  apply andb_prop in Hrest as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  apply (meta_tile_neverqhtr tm Z (fun K => cp_kmin cert <= K)
           (fun K => bsem tbl (fun _ => K) (btplp_cfg cert))
           (fun K => cp_a cert * K + cp_b cert) F (cp_anchor cert)
           (cp_k0 cert) (q1, (l1, h1, r1)) tvis); [| exact Hkk | | | exact Hanchv | exact Hpre].
  - (* the anchor *)
    rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold bsem, bdcfg, btplp_cfg. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity.
  - (* the parameter stays admissible *)
    intros K HK. nia.
  - (* the cycle *)
    intros K HK.
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
    exact HR.
Qed.

Corollary irulesblkpfx_check_neverqhtr_v5c_nonhalt : forall tm cert cfuel fuel,
  irulesblkpfx_check_neverqhtr_v5c tm cert cfuel fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_tr_nonhalt, irulesblkpfx_check_neverqhtr_v5c_sound; eauto.
Qed.
