(** * IRules.MetaQH: the quasihalting corollary of the IRules meta model.

    The dual extraction lemma of [Meta.irules_check_neverqh] (SWEEP
    2026-07-21 SS6 step 3).  The v1 inductive-rules certificate builds a
    faithful forward-behavior model of the machine from its anchor on:
    the meta-cycle induction shows that every configuration from the
    anchor fires a transition in the cycle's fired set [F], and every
    transition in [F] fires unboundedly often.  [Meta] extracts
    [NeverQuasiHaltsSt] when every prefix-visited state owns a
    transition in [F].  This file extracts the OTHER conclusion from
    the SAME model: when a prefix-visited state [qz] owns NO transition
    in [F], it is never visited from the anchor on -- the machine
    provably quasihalts with [qz] as the silent-state witness.

    The checker reuses the whole landed engine verbatim -- certificate
    record, rule validation ([check_rules]), symbolic meta replay
    ([replay]), anchor re-simulation, denotation shift ([want_shift]).
    Only the final property lemma is new; no existing file is touched.

    Beyond [QuasiHaltsSt] the census R_QH contract also needs
    [QHBound B] (EVERY quiet state's last visit < [B], [B] = 2000 <<
    anchor ~ 2e5).  States in [F] recur unboundedly, so they are never
    quiet; states outside [F] are unvisited from the anchor on, so
    their last visit is < anchor -- but that alone only gives
    [QHBound anchor].  The checker therefore also verifies the score
    WINDOW: no state outside [F] is visited at any index in
    [min B anchor, anchor) (a [cvisits] pass from the step-[min B anchor]
    configuration).  Every quiet state's last visit is then
    < min B anchor <= B.

    Soundness gives the full census tier triple
    [NonHalt /\ QHBound B /\ QuasiHaltsSt].

    [Print Assumptions irules_check_qh_sound] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta.
Import ListNotations.
Open Scope Z_scope.

(** ** The checker

    [irules_check_qh tm cert qz B fuel]: checks 1-3 of
    [Meta.irules_check_neverqh] (rule validation, anchor
    re-simulation against [C(k0)], symbolic meta-cycle replay to
    [C(a*k+b)] under the inward meta map), then instead of check 4
    (all prefix states in [F]):

    4'. [qz] is visited in the prefix but owns no transition in [F]
        (the quasihalt witness), and
    5'. no state outside [F] is visited in the window
        [min B anchor, anchor)  (the score bound). *)

Definition irules_check_qh (tm : TM) (cert : IRCert) (qz : St)
  (B : nat) (fuel : nat) : bool :=
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
          match csteps tm (c_anchor cert) c0 with
          | Some (q, (l, h, r)) =>
              st_eqb q (c_st cert) && sym_eqb h (c_hs cert) &&
              lpad_eqb l (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TL cert))) &&
              lpad_eqb r (dside (fun _ => c_k0 cert)
                            (tpl_start (c_TR cert))) &&
              cvisits tm c0 (c_anchor cert) qz &&
              negb (st_in qz F) &&
              match csteps tm (Nat.min B (c_anchor cert)) c0 with
              | Some cB =>
                  forallb (fun q' =>
                             implb (cvisits tm cB
                                      (c_anchor cert - Nat.min B (c_anchor cert))%nat
                                      q')
                                   (st_in q' F)) all_St
              | None => false
              end
          | None => false
          end
      end
  end.

(** ** Soundness *)

Lemma st_in_complete : forall q t F,
  In t F -> fst t = q -> st_in q F = true.
Proof.
  intros q t F Hin Hq.
  apply existsb_exists. exists t. split; [exact Hin|].
  apply st_eqb_spec. exact Hq.
Qed.

Lemma fst_trans_of : forall c, fst (trans_of c) = fst c.
Proof. reflexivity. Qed.

(** The middle conjunct IS [QHBound B tm] (Census/TNF_QH.v defines
    [QHBound B tm := forall q s, QuietAfter tm q s -> S s <= B]); it is
    stated unfolded here so the checker stays in the Checkers layer,
    below the census (same convention as [Wrap.ngram_check_qhbound_sound]). *)
Theorem irules_check_qh_sound : forall tm cert qz B fuel,
  irules_check_qh tm cert qz B fuel = true ->
  NonHalt tm /\ (forall q s, QuietAfter tm q s -> (S s <= B)%nat) /\
  QuasiHaltsSt tm.
Proof.
  intros tm cert qz B fuel H.
  unfold irules_check_qh in H.
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
  destruct (csteps tm (c_anchor cert) c0) as [[q1 [[l1 h1] r1]]|]
    eqn:Hanch; [|discriminate].
  set (W0 := Nat.min B (c_anchor cert)) in *.
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
  (* single-index coverage: every index >= anchor fires a transition in F *)
  assert (Hcover : forall m, (c_anchor cert <= m)%nat ->
    exists cm, stepn tm m InitES = Some cm /\ In (trans_of cm) F).
  { intros m Hm.
    destruct (Htiles (m + 1 - c_anchor cert)%nat)
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
  assert (Hlive : forall q n, (c_anchor cert <= n)%nat ->
    VisitsAt tm q n -> st_in q F = true).
  { intros q n Hn (c & Hc & Hq).
    destruct (Hcover n Hn) as (cm & Hcm & Hin).
    rewrite Hc in Hcm. injection Hcm as <-.
    exact (st_in_complete q _ F Hin
             (eq_trans (fst_trans_of c) Hq)). }
  (* a state visited inside the score window [W0, anchor) owns a
     transition in F *)
  assert (Hwindow : forall q n, (W0 <= n)%nat -> (n < c_anchor cert)%nat ->
    VisitsAt tm q n -> st_in q F = true).
  { intros q n Hn1 Hn2 (c & Hc & Hq).
    destruct (stepn_csteps tm n c Hc) as (cc & Hcc & Hlift).
    replace n with (W0 + (n - W0))%nat in Hcc by lia.
    rewrite csteps_add, HcB in Hcc.
    assert (Hfst : fst cc = q).
    { rewrite <- Hq, <- Hlift. reflexivity. }
    assert (Hv : cvisits tm cB (c_anchor cert - W0) q = true).
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
        destruct (Nat.lt_ge_cases s (c_anchor cert)) as [Hlt|Hge2].
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
    + exists (c_anchor cert).
      intros n Hn Hvis.
      rewrite (Hlive qz n Hn Hvis) in HwitF. discriminate.
Qed.

Corollary irules_check_qh_quasihalts : forall tm cert qz B fuel,
  irules_check_qh tm cert qz B fuel = true -> QuasiHaltsSt tm.
Proof.
  intros tm cert qz B fuel H.
  exact (proj2 (proj2 (irules_check_qh_sound tm cert qz B fuel H))).
Qed.

Corollary irules_check_qh_nonhalt : forall tm cert qz B fuel,
  irules_check_qh tm cert qz B fuel = true -> NonHalt tm.
Proof.
  intros tm cert qz B fuel H.
  exact (proj1 (irules_check_qh_sound tm cert qz B fuel H)).
Qed.
