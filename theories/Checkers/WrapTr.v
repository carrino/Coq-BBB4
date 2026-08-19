(** * Checkers/WrapTr: quiet-INSTRUCTION quasihalting via the
    one-cell halt-redirect machine.

    Wrap.v's halt-redirect argument at transition level
    (SCOPING_INSTR.md sections 3.2, 5): to prove instruction [tg]
    quiet after step [s], blank exactly ONE table cell ([tm_wrap_tr])
    and build a halt-free closure of the wrapped machine from the real
    machine's step-[t] configuration.  A configuration about to fire
    [tg] has no successor in the wrapped machine, so halt-freeness
    says the wrapped run never fires [tg] — and off [tg] the two
    machines agree step for step ([wrap_tr_agree]).  Crucially the
    construction is correct for a STILL-RUNNING state: the wrapped
    machine keeps executing [fst tg] on the other symbol, which is
    exactly what the state-level wrap could not express.

    [ngram_check_qhboundtr] adds the ClosureTr rank-liveness gate over
    the same wrapped closure and delivers the census R_QH contract at
    transition level:

      [NonHalt tm /\ QHBoundTr (S t) tm /\ QuasiHaltsTr tm]

    (the middle conjunct stated unfolded, keeping this file below the
    census layer). *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Closure ClosureTr.
From BBB4.Checkers Require Import Cycle NGram NGramTr.
From BBB4.Checkers.IRules Require Import Engine AnchorVisits AnchorVisitsTr.
Import ListNotations.
Open Scope nat_scope.

(** ** The one-cell halt-redirect machine *)

Definition tm_wrap_tr (tm : TM) (tg : Instr) : TM :=
  fun p x => if instr_eqb (p, x) tg then None else tm p x.

Lemma tm_wrap_tr_at : forall tm tg,
  tm_wrap_tr tm tg (fst tg) (snd tg) = None.
Proof.
  intros tm [q a]. unfold tm_wrap_tr; simpl.
  now rewrite (proj2 (instr_eqb_spec (q, a) (q, a)) eq_refl).
Qed.

Lemma tm_wrap_tr_off : forall tm tg p x,
  (p, x) <> tg -> tm_wrap_tr tm tg p x = tm p x.
Proof.
  intros tm tg p x H. unfold tm_wrap_tr.
  destruct (instr_eqb (p, x) tg) eqn:E; [|reflexivity].
  apply instr_eqb_spec in E. contradiction.
Qed.

Lemma wrap_tr_step_off : forall tm tg c,
  instr_of c <> tg -> step (tm_wrap_tr tm tg) c = step tm c.
Proof.
  intros tm tg [p tp] H. unfold step; simpl in *.
  rewrite tm_wrap_tr_off; [reflexivity|].
  exact H.
Qed.

Lemma wrap_tr_step_at : forall tm tg c,
  instr_of c = tg -> step (tm_wrap_tr tm tg) c = None.
Proof.
  intros tm tg [p tp] H. unfold instr_of in H; simpl in H.
  unfold step; simpl.
  replace (tm_wrap_tr tm tg p (t_head tp)) with (@None Trans);
    [reflexivity|].
  rewrite <- H. symmetry.
  exact (tm_wrap_tr_at tm (p, t_head tp)).
Qed.

(** While the wrapped run survives, the two runs coincide and never
    fire [tg]. *)
Lemma wrap_tr_agree : forall tm tg c,
  (forall j, stepn (tm_wrap_tr tm tg) j c <> None) ->
  forall k, stepn (tm_wrap_tr tm tg) k c = stepn tm k c /\
            (forall c', stepn tm k c = Some c' -> instr_of c' <> tg).
Proof.
  intros tm tg c Him k. induction k as [|k IH].
  - split; [reflexivity|].
    intros c' Hc' Hq. simpl in Hc'. injection Hc' as <-.
    apply (Him 1). cbn [stepn].
    rewrite wrap_tr_step_at by assumption. reflexivity.
  - destruct IH as [IHeq IHq].
    destruct (stepn (tm_wrap_tr tm tg) k c) as [ck|] eqn:Ek;
      [| now destruct (Him k)].
    assert (Hck : stepn tm k c = Some ck) by congruence.
    assert (Hoff : instr_of ck <> tg) by (apply (IHq ck Hck)).
    assert (Heq : stepn (tm_wrap_tr tm tg) (S k) c = stepn tm (S k) c).
    { replace (S k) with (k + 1) by lia.
      rewrite !stepn_add, Ek, Hck. cbn [stepn].
      rewrite wrap_tr_step_off by assumption. reflexivity. }
    split; [exact Heq|].
    intros c' Hc' Hq'.
    apply (Him (S k + 1)).
    rewrite stepn_add, Heq, Hc'. cbn [stepn].
    rewrite wrap_tr_step_at by assumption. reflexivity.
Qed.

(** ** The checker *)

(** Halt-free wrapped closure with the ClosureTr rank-liveness gate. *)
Definition wrap_closed_live_tr (tmw : TM) (lset rset : gset)
    (fuel : nat) (a0 : cconf) : bool :=
  match close_tr cconf cconf_enc (ng_succs tmw lset rset)
              fuel [] PositiveSet.empty [a0] with
  | Some Sl =>
      closed_tr_b cconf cconf_enc (ng_succs tmw lset rset) Sl &&
      mem_tr cconf cconf_enc a0 Sl &&
      live_ok_tr cconf cconf_enc cinstr (ng_succs tmw lset rset) Sl
  | None => false
  end.

Definition ngram_check_qhboundtr (tm : TM) (tg : Instr)
    (s n t fuel rounds : nat) : bool :=
  (1 <=? n) && (s <? t) &&
  match csteps tm t c0, csteps tm s c0 with
  | Some ct, Some cs =>
      instr_eqb (cinstr cs) tg &&
      match cstep tm cs with
      | Some cs1 => negb (cfires tm cs1 (t - s) tg)
      | None => false
      end &&
      let tmw := tm_wrap_tr tm tg in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) := ng_grow tmw a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset ct &&
      wrap_closed_live_tr tmw lset rset fuel a0
  | _, _ => false
  end.

(** ** Soundness *)

Theorem ngram_check_qhboundtr_sound : forall tm tg s n t fuel rounds,
  ngram_check_qhboundtr tm tg s n t fuel rounds = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm tg s n t fuel rounds H.
  unfold ngram_check_qhboundtr in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [Hn Hst].
  apply Nat.leb_le in Hn. apply Nat.ltb_lt in Hst.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
  destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
  apply andb_prop in Hrest as [H Hcl].
  apply andb_prop in H as [Hqs Hnv].
  apply instr_eqb_spec in Hqs.
  destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
  apply negb_true_iff in Hnv.
  destruct ct as [q1 [[l h] r]] eqn:Ectc.
  match type of Hcl with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in Hcl.
  apply andb_prop in Hcl as [Hseed Hwc].
  rewrite <- Ectc in *.
  set (tmw := tm_wrap_tr tm tg) in *.
  unfold wrap_closed_live_tr in Hwc.
  destruct (close_tr cconf cconf_enc (ng_succs tmw lset rset)
                  fuel [] PositiveSet.empty [ng_start n ct])
    as [Sl|] eqn:Ecl; [|discriminate].
  apply andb_prop in Hwc as [Hwc Hlive].
  apply andb_prop in Hwc as [Hclb Hmem].
  apply mem_In_tr in Hmem; [|exact cconf_enc_inj].
  assert (Hcov0 : ng_covers n lset rset (ng_start n ct) (lift ct)).
  { apply ng_start_covers. subst ct. exact Hseed. }
  set (SS := fun a c Hc => ng_succs_sound tmw n lset rset a c Hn Hc).
  set (CST := fun a c (Hc : ng_covers n lset rset a c) =>
                ng_covers_instr n lset rset a c Hc).
  assert (Him : forall k, stepn tmw k (lift ct) <> None).
  { intros k HN.
    destruct (closure_invariant_tr tmw cconf cconf_enc
                (ng_succs tmw lset rset) (ng_covers n lset rset)
                cconf_enc_inj SS
                Sl Hclb (ng_start n ct) (lift ct) Hmem Hcov0 k)
      as (c' & a' & Hst' & _ & _).
    congruence. }
  assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
  { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
  assert (Hstept : stepn tm t InitES = Some (lift ct)).
  { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
  assert (Hquiet : forall m, s < m -> ~ FiresAt tm tg m).
  { intros m Hm (c & Hc & Hcq).
    destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
    assert (Hccq : cinstr cc = tg).
    { rewrite <- cinstr_lift, Hlift. exact Hcq. }
    destruct (le_lt_dec m t) as [Hle | Hgt].
    - replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
      rewrite csteps_add, Ecs1' in Hcc.
      rewrite (cfires_complete tm (t - s) cs1 tg (m - s - 1) cc)
        in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
    - replace m with (t + (m - t)) in Hcc by lia.
      rewrite csteps_add, Ect in Hcc.
      apply csteps_lift in Hcc.
      destruct (wrap_tr_agree tm tg (lift ct) Him (m - t)) as [_ Hqfree].
      apply (Hqfree (lift cc)); [exact Hcc|].
      rewrite cinstr_lift. exact Hccq. }
  assert (Hvis : FiresAt tm tg s).
  { exists (lift cs). split.
    - rewrite <- lift_c0. apply csteps_lift. exact Ecs.
    - rewrite cinstr_lift. exact Hqs. }
  assert (HNonHalt : NonHalt tm).
  { intros m HN.
    destruct (le_lt_dec m t) as [Hle | Hgt].
    + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
      apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
    + replace m with (t + (m - t)) in HN by lia.
      rewrite stepn_add, Hstept in HN.
      destruct (wrap_tr_agree tm tg (lift ct) Him (m - t)) as [Heq _].
      rewrite <- Heq in HN.
      exact (Him (m - t) HN). }
  split; [exact HNonHalt | split].
  - (* QHBoundTr (S t): every quiet instruction's last fire is <= t *)
    intros tg'' s'' [Hvis'' Hlast''].
    apply le_n_S.
    destruct (le_lt_dec s'' t) as [Hle | Hgt]; [exact Hle | exfalso].
    destruct Hvis'' as (c & Hc & Hcq).
    destruct (stepn_csteps tm s'' c) as (cc & Hcc & Hlift); [exact Hc|].
    assert (Hccq : instr_of (lift cc) = tg'').
    { rewrite Hlift. exact Hcq. }
    assert (Hcw : stepn tm (s'' - t) (lift ct) = Some (lift cc)).
    { replace s'' with (t + (s'' - t)) in Hc by lia.
      rewrite stepn_add, Hstept in Hc. rewrite Hc, Hlift. reflexivity. }
    assert (Hwrun : stepn tmw (s'' - t) (lift ct) = Some (lift cc)).
    { destruct (wrap_tr_agree tm tg (lift ct) Him (s'' - t)) as [Heq _].
      transitivity (stepn tm (s'' - t) (lift ct)); [exact Heq | exact Hcw]. }
    assert (Happ : appears_tr cconf cinstr Sl tg'' = true).
    { rewrite <- Hccq.
      apply (live_fired_appears_tr tmw cconf cconf_enc cinstr
               (ng_succs tmw lset rset) (ng_covers n lset rset)
               cconf_enc_inj CST SS
               Sl (ng_start n ct) (lift ct) Hclb Hmem Hcov0
               (s'' - t) (lift cc) Hwrun). }
    destruct (live_appears_recur_tr tmw cconf cconf_enc cinstr
                (ng_succs tmw lset rset) (ng_covers n lset rset)
                cconf_enc_inj CST SS
                Sl (ng_start n ct) (lift ct) tg'' Hclb Hlive Hmem Hcov0 Happ
                (S s'' - t)) as (k & c' & Hk & Hstepk & Hqk).
    assert (Hstm : stepn tm k (lift ct) = Some c').
    { destruct (wrap_tr_agree tm tg (lift ct) Him k) as [Heqk _].
      rewrite <- Heqk. exact Hstepk. }
    apply (Hlast'' (t + k)); [lia|].
    exists c'. split; [| exact Hqk].
    rewrite stepn_add, Hstept. exact Hstm.
  - eapply quiet_after_tr_qh. split; [exact Hvis | exact Hquiet].
Qed.
