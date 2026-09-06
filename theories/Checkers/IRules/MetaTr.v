(** * IRules.MetaTr: the meta-cycle checker at TRANSITION level.

    The instruction-level port of Meta.v's [irules_check_neverqh]
    (SCOPING_INSTR.md sections 3.2, 7): the engine's [Reach] already
    carries per-instruction cover ([Covers]) and per-instruction
    recurrence ([Fires]) -- Meta.v's state-level conclusion only
    PROJECTED them down through [st_in].  This checker keeps them:

    - the fired set [F] recurs per INSTRUCTION ([Hrec] below), and
      every configuration from the anchor on fires an instruction in
      [F], both exactly as in Meta.v;
    - the prefix gate strengthens: instead of "every state VISITED in
      the prefix has some transition in [F]" ([st_in]), it requires
      "every instruction FIRED in the prefix is in [F]" (the
      [AnchorVisitsTr] mask).  This is the strictly stronger check --
      and its failure on a certificate that passes Meta.v's checker is
      precisely a VERDICT FLIP: the machine never quasihalts at state
      level yet transition-quasihalts, its quiet instructions being
      the prefix-fired ones outside [F] (all with last fire before the
      anchor).

    Same certificates ([IRCert]), same replay, same fuel discipline;
    only the mask and the conclusion change. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules
  AnchorVisits AnchorVisitsTr Meta.
Import ListNotations.
Open Scope Z_scope.

Set Default Goal Selector "!".

Lemma trans_of_instr_of : forall c, trans_of c = instr_of c.
Proof. reflexivity. Qed.

Definition tr_in (t : Tr) (F : list Tr) : bool :=
  existsb (instr_eqb t) F.

Lemma tr_in_sound : forall t F, tr_in t F = true -> In t F.
Proof.
  intros t F H.
  apply existsb_exists in H as (t' & Hin & Ht).
  apply instr_eqb_spec in Ht. subst t'. exact Hin.
Qed.

(** ** The checker: Meta.v's, with the instruction-mask prefix gate *)

Definition irules_check_neverqhtr (tm : TM) (cert : IRCert) (fuel : nat)
  : bool :=
  (0 <=? c_kmin cert) && (c_kmin cert <=? c_k0 cert) &&
  (0 <=? c_a cert) &&
  (c_kmin cert <=? c_a cert * c_kmin cert + c_b cert) &&
  match check_rules tm fuel (c_rules cert) with
  | None => false
  | Some rules =>
      match replay tm [c_kmin cert] rules
              (fun c => scfg_eqb c (want_cfg cert))
              fuel false (tpl_cfg cert) with
      | None => false
      | Some (_, F) =>
          match csteps_tvis tm (c_anchor cert) c0 tvm_empty with
          | Some (q, (l, h, r), tvis) =>
              st_eqb q (c_st cert) && sym_eqb h (c_hs cert) &&
              lpad_eqb l (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TL cert))) &&
              lpad_eqb r (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TR cert))) &&
              forallb (fun t =>
                         implb (tvm_get tvis t)
                               (tr_in t F)) all_Instr
          | None => false
          end
      end
  end.

(** ** Soundness *)

Theorem irules_check_neverqhtr_sound : forall tm cert fuel,
  irules_check_neverqhtr tm cert fuel = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm cert fuel H.
  unfold irules_check_neverqhtr in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hinward].
  apply andb_prop in H as [H Ha0].
  apply andb_prop in H as [Hk0 Hkk].
  apply Z.leb_le in Hk0, Hkk, Ha0, Hinward.
  destruct (check_rules tm fuel (c_rules cert)) as [rules|] eqn:Hcr;
    [|discriminate].
  destruct (replay tm [c_kmin cert] rules
              (fun c => scfg_eqb c (want_cfg cert))
              fuel false (tpl_cfg cert)) as [[cend F]|] eqn:Hrep;
    [|discriminate].
  destruct (csteps_tvis tm (c_anchor cert) c0 tvm_empty)
    as [[[q1 [[l1 h1] r1]] tvis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_tvis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
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
    destruct (replay_sound tm [c_kmin cert] rules _ fuel false
                (tpl_cfg cert) cend F Hrep (fun _ => K) Hb)
      as (Hend & n & HR & Hpos).
    { intros r Fr c1 c2 Hin Happ.
      exact (rule_apply_sound tm [c_kmin cert] r Fr c1 c2 Happ
               (check_rules_sound tm fuel _ _ Hcr r Fr Hin)
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
  (* the transition-level never-quasihalting argument *)
  intros t0 Hf B.
  (* a fired instruction is in the cycle's fired set *)
  assert (Ht0 : In t0 F).
  { destruct Hf as (n0 & cn & Hcn & Htc).
    destruct (Nat.lt_ge_cases n0 (c_anchor cert)) as [Hlt | Hge].
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
      destruct (Htiles (n0 + 1 - c_anchor cert)%nat)
        as (N & K & HN & HK & Hstep & Hcov).
      destruct (Hcov n0 Hge ltac:(lia)) as (cm & Hcm & Hin).
      rewrite Hcn in Hcm. injection Hcm as <-.
      rewrite trans_of_instr_of, Htc in Hin. exact Hin. }
  destruct (Hrec t0 Ht0 B) as (m & cm & Hm & Hcm & Htr).
  exists m. split; [exact Hm|].
  exists cm. split; [exact Hcm|].
  rewrite <- trans_of_instr_of. exact Htr.
Qed.

Corollary irules_check_neverqhtr_nonhalt : forall tm cert fuel,
  irules_check_neverqhtr tm cert fuel = true -> NonHalt tm.
Proof.
  intros. eapply never_qh_tr_nonhalt, irules_check_neverqhtr_sound; eauto.
Qed.
