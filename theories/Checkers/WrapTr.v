(** * Checkers/WrapTr: quiet-INSTRUCTION quasihalting via the
    multi-cell halt-redirect machine.

    Wrap.v's halt-redirect argument at transition level
    (SCOPING_INSTR.md sections 3.2, 5).  The load-bearing difference
    from the state level, measured on the v0 suspects: a
    transition-quasihalting machine typically has SEVERAL quiet
    instructions (a quiet state contributes two at once, plus
    stragglers), and a closure wrapped at only one of them keeps the
    others as appearing-but-never-recurring nodes — the liveness gate
    then rightly fails.  So the wrap blanks the machine's whole
    CLAIMED-QUIET SET [tgs] ([tm_wrap_trs]): a halt-free closure of
    that machine says none of them ever fires after [t], and the
    ClosureTr rank gate over the same closure makes every OTHER
    appearing instruction recur.  Each pair [(tg, s)] in [tgs] is
    additionally pinned by simulation: [tg] fires at [s] and not in
    [(s, t]].

    Delivered (census R_QH contract at transition level):

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

(** ** The multi-cell halt-redirect machine *)

Definition tr_inb (t : Instr) (tgs : list Instr) : bool :=
  existsb (instr_eqb t) tgs.

Lemma tr_inb_spec : forall t tgs, tr_inb t tgs = true <-> In t tgs.
Proof.
  intros t tgs. unfold tr_inb. rewrite existsb_exists.
  split.
  - intros (t' & Hin & He). apply instr_eqb_spec in He. now subst.
  - intros Hin. exists t. split; [exact Hin|].
    apply instr_eqb_spec; reflexivity.
Qed.

Definition tm_wrap_trs (tm : TM) (tgs : list Instr) : TM :=
  fun p x => if tr_inb (p, x) tgs then None else tm p x.

Lemma tm_wrap_trs_at : forall tm tgs p x,
  In (p, x) tgs -> tm_wrap_trs tm tgs p x = None.
Proof.
  intros tm tgs p x H. unfold tm_wrap_trs.
  now rewrite (proj2 (tr_inb_spec (p, x) tgs) H).
Qed.

Lemma tm_wrap_trs_off : forall tm tgs p x,
  ~ In (p, x) tgs -> tm_wrap_trs tm tgs p x = tm p x.
Proof.
  intros tm tgs p x H. unfold tm_wrap_trs.
  destruct (tr_inb (p, x) tgs) eqn:E; [|reflexivity].
  apply tr_inb_spec in E. contradiction.
Qed.

Lemma wrap_trs_step_off : forall tm tgs c,
  ~ In (instr_of c) tgs -> step (tm_wrap_trs tm tgs) c = step tm c.
Proof.
  intros tm tgs [p tp] H. unfold step; simpl in *.
  rewrite tm_wrap_trs_off; [reflexivity | exact H].
Qed.

Lemma wrap_trs_step_at : forall tm tgs c,
  In (instr_of c) tgs -> step (tm_wrap_trs tm tgs) c = None.
Proof.
  intros tm tgs [p tp] H. unfold instr_of in H; simpl in H.
  unfold step; simpl.
  now rewrite (tm_wrap_trs_at tm tgs p (t_head tp) H).
Qed.

(** While the wrapped run survives, the two runs coincide and never
    fire anything in [tgs]. *)
Lemma wrap_trs_agree : forall tm tgs c,
  (forall j, stepn (tm_wrap_trs tm tgs) j c <> None) ->
  forall k, stepn (tm_wrap_trs tm tgs) k c = stepn tm k c /\
            (forall c', stepn tm k c = Some c' -> ~ In (instr_of c') tgs).
Proof.
  intros tm tgs c Him k. induction k as [|k IH].
  - split; [reflexivity|].
    intros c' Hc' Hq. simpl in Hc'. injection Hc' as <-.
    apply (Him 1). cbn [stepn].
    rewrite wrap_trs_step_at by assumption. reflexivity.
  - destruct IH as [IHeq IHq].
    destruct (stepn (tm_wrap_trs tm tgs) k c) as [ck|] eqn:Ek;
      [| now destruct (Him k)].
    assert (Hck : stepn tm k c = Some ck) by congruence.
    assert (Hoff : ~ In (instr_of ck) tgs) by (apply (IHq ck Hck)).
    assert (Heq : stepn (tm_wrap_trs tm tgs) (S k) c = stepn tm (S k) c).
    { replace (S k) with (k + 1) by lia.
      rewrite !stepn_add, Ek, Hck. cbn [stepn].
      rewrite wrap_trs_step_off by assumption. reflexivity. }
    split; [exact Heq|].
    intros c' Hc' Hq'.
    apply (Him (S k + 1)).
    rewrite stepn_add, Heq, Hc'. cbn [stepn].
    rewrite wrap_trs_step_at by assumption. reflexivity.
Qed.

(** ** The checker *)

(** per-pair prefix pinning: [tg] fires at [s] and not in [(s, t]] *)
Definition wrap_pin_ok (tm : TM) (t : nat) (p : Instr * nat) : bool :=
  let '(tg, s) := p in
  (s <? t) &&
  match csteps tm s c0 with
  | Some cs =>
      instr_eqb (cinstr cs) tg &&
      match cstep tm cs with
      | Some cs1 => negb (cfires tm cs1 (t - s) tg)
      | None => false
      end
  | None => false
  end.

(** halt-free wrapped closure with the ClosureTr rank-liveness gate *)
Definition wrap_closed_live_trs (tmw : TM) (lset rset : gset)
    (fuel : nat) (a0 : cconf) : bool :=
  match close_tr cconf cconf_enc (ng_succs tmw lset rset)
              fuel [] PositiveSet.empty [a0] with
  | Some Sl =>
      closed_tr_b cconf cconf_enc (ng_succs tmw lset rset) Sl &&
      mem_tr cconf cconf_enc a0 Sl &&
      live_ok_tr cconf cconf_enc cinstr (ng_succs tmw lset rset) Sl
  | None => false
  end.

Definition ngram_check_qhboundtr (tm : TM) (tgs : list (Instr * nat))
    (n t fuel rounds : nat) : bool :=
  (1 <=? n) && (1 <=? length tgs) &&
  forallb (wrap_pin_ok tm t) tgs &&
  match csteps tm t c0 with
  | Some ct =>
      let tmw := tm_wrap_trs tm (map fst tgs) in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) := ng_grow tmw a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset ct &&
      wrap_closed_live_trs tmw lset rset fuel a0
  | None => false
  end.

(** lex-gated variant: each appearing instruction is discharged by
    plain acyclicity OR a lexicographic [ngcomp] certificate (the
    never-QH lex tier's measure vocabulary), lifting the wrapped
    closures whose recurrent part needs a measure argument -- on the
    v0 suspects that is nearly all of them: a sweeping machine's
    abstract closure self-loops inside its uniform runs, so a plain
    rank for any OTHER instruction cannot exist. *)
Definition wrap_closed_live_lex_trs (tm : TM) (n : nat)
    (tmw : TM) (lset rset : gset)
    (fuel : nat) (a0 : cconf) (cert : Instr -> list ngcomp) : bool :=
  match close_tr cconf cconf_enc (ng_succs tmw lset rset)
              fuel [] PositiveSet.empty [a0] with
  | Some Sl =>
      closed_tr_b cconf cconf_enc (ng_succs tmw lset rset) Sl &&
      mem_tr cconf cconf_enc a0 Sl &&
      live_lex_ok_tr cconf cconf_enc cinstr (ng_succs tmw lset rset) Sl
        (fun tg' => map (ng_comp_denote tmw n) (cert tg'))
  | None => false
  end.

Definition ngram_check_qhboundtr_lex (tm : TM) (tgs : list (Instr * nat))
    (n t fuel rounds : nat) (cert : Instr -> list ngcomp) : bool :=
  (1 <=? n) && (1 <=? length tgs) &&
  forallb (wrap_pin_ok tm t) tgs &&
  match csteps tm t c0 with
  | Some ct =>
      let tmw := tm_wrap_trs tm (map fst tgs) in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) := ng_grow tmw a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset ct &&
      wrap_closed_live_lex_trs tm n tmw lset rset fuel a0 cert
  | None => false
  end.

(** ** Soundness *)

Theorem ngram_check_qhboundtr_sound : forall tm tgs n t fuel rounds,
  ngram_check_qhboundtr tm tgs n t fuel rounds = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm tgs n t fuel rounds H.
  unfold ngram_check_qhboundtr in H.
  apply andb_prop in H as [H Hcl].
  apply andb_prop in H as [H Hpins].
  apply andb_prop in H as [Hn Hlen].
  apply Nat.leb_le in Hn. apply Nat.leb_le in Hlen.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
  destruct ct as [q1 [[l h] r]] eqn:Ectc.
  match type of Hcl with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in Hcl.
  apply andb_prop in Hcl as [Hseed Hwc].
  rewrite <- Ectc in *.
  set (W := map fst tgs) in *.
  set (tmw := tm_wrap_trs tm W) in *.
  unfold wrap_closed_live_trs in Hwc.
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
  assert (Hstept : stepn tm t InitES = Some (lift ct)).
  { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
  rewrite forallb_forall in Hpins.
  (* each pinned instruction: fires at its s, never after it *)
  assert (Hpinned : forall tg s, In (tg, s) tgs ->
    FiresAt tm tg s /\ (forall m, s < m -> ~ FiresAt tm tg m)).
  { intros tg s Hin.
    specialize (Hpins (tg, s) Hin).
    unfold wrap_pin_ok in Hpins.
    apply andb_prop in Hpins as [Hst Hpins].
    apply Nat.ltb_lt in Hst.
    destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
    apply andb_prop in Hpins as [Hqs Hnv].
    apply instr_eqb_spec in Hqs.
    destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
    apply negb_true_iff in Hnv.
    assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
    { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
    split.
    - exists (lift cs). split.
      + rewrite <- lift_c0. apply csteps_lift. exact Ecs.
      + rewrite cinstr_lift. exact Hqs.
    - intros m Hm (c & Hc & Hcq).
      destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
      assert (Hccq : cinstr cc = tg).
      { rewrite <- cinstr_lift, Hlift. exact Hcq. }
      destruct (le_lt_dec m t) as [Hle | Hgt].
      + replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
        rewrite csteps_add, Ecs1' in Hcc.
        rewrite (cfires_complete tm (t - s) cs1 tg (m - s - 1) cc)
          in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
      + replace m with (t + (m - t)) in Hcc by lia.
        rewrite csteps_add, Ect in Hcc.
        apply csteps_lift in Hcc.
        destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [_ Hqfree].
        apply (Hqfree (lift cc)); [exact Hcc|].
        rewrite cinstr_lift, Hccq.
        apply in_map_iff. exists (tg, s). split; [reflexivity | exact Hin]. }
  assert (HNonHalt : NonHalt tm).
  { intros m HN.
    destruct (le_lt_dec m t) as [Hle | Hgt].
    + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
      apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
    + replace m with (t + (m - t)) in HN by lia.
      rewrite stepn_add, Hstept in HN.
      destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [Heq _].
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
    (* the fire at s'' > t sits on the wrapped run, so tg'' is not in
       the wrapped set *)
    assert (Hcw : stepn tm (s'' - t) (lift ct) = Some (lift cc)).
    { replace s'' with (t + (s'' - t)) in Hc by lia.
      rewrite stepn_add, Hstept in Hc. rewrite Hc, Hlift. reflexivity. }
    assert (Hwrun : stepn tmw (s'' - t) (lift ct) = Some (lift cc)).
    { destruct (wrap_trs_agree tm W (lift ct) Him (s'' - t)) as [Heq _].
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
    { destruct (wrap_trs_agree tm W (lift ct) Him k) as [Heqk _].
      rewrite <- Heqk. exact Hstepk. }
    apply (Hlast'' (t + k)); [lia|].
    exists c'. split; [| exact Hqk].
    rewrite stepn_add, Hstept. exact Hstm.
  - (* the QH witness: any pinned pair *)
    destruct tgs as [| [tg s] rest]; [simpl in Hlen; lia|].
    destruct (Hpinned tg s (or_introl eq_refl)) as [Hf Hq].
    eapply quiet_after_tr_qh. split; [exact Hf | exact Hq].
Qed.

Theorem ngram_check_qhboundtr_lex_sound :
  forall tm tgs n t fuel rounds cert,
  ngram_check_qhboundtr_lex tm tgs n t fuel rounds cert = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm tgs n t fuel rounds cert H.
  unfold ngram_check_qhboundtr_lex in H.
  apply andb_prop in H as [H Hcl].
  apply andb_prop in H as [H Hpins].
  apply andb_prop in H as [Hn Hlen].
  apply Nat.leb_le in Hn. apply Nat.leb_le in Hlen.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
  destruct ct as [q1 [[l h] r]] eqn:Ectc.
  match type of Hcl with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in Hcl.
  apply andb_prop in Hcl as [Hseed Hwc].
  rewrite <- Ectc in *.
  set (W := map fst tgs) in *.
  set (tmw := tm_wrap_trs tm W) in *.
  unfold wrap_closed_live_lex_trs in Hwc.
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
  (* the denoted certificate components are exact for the WRAPPED
     machine (the measure lemmas are generic in the machine) *)
  assert (Hexd : forall tg0,
    Forall (comp_exact tmw cconf (ng_succs tmw lset rset)
              (ng_covers n lset rset))
           (map (ng_comp_denote tmw n) (cert tg0))).
  { intros tg0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    - exact I.
    - intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply (ngm_exact tmw n lset rset); eauto.
    - exact I.
    - destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply (pm_exact tmw n lset rset); eauto.
      + apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      + destruct rg; apply Nat.leb_le; assumption. }
  assert (Him : forall k, stepn tmw k (lift ct) <> None).
  { intros k HN.
    destruct (closure_invariant_tr tmw cconf cconf_enc
                (ng_succs tmw lset rset) (ng_covers n lset rset)
                cconf_enc_inj SS
                Sl Hclb (ng_start n ct) (lift ct) Hmem Hcov0 k)
      as (c' & a' & Hst' & _ & _).
    congruence. }
  assert (Hstept : stepn tm t InitES = Some (lift ct)).
  { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
  rewrite forallb_forall in Hpins.
  assert (Hpinned : forall tg s, In (tg, s) tgs ->
    FiresAt tm tg s /\ (forall m, s < m -> ~ FiresAt tm tg m)).
  { intros tg s Hin.
    specialize (Hpins (tg, s) Hin).
    unfold wrap_pin_ok in Hpins.
    apply andb_prop in Hpins as [Hst Hpins].
    apply Nat.ltb_lt in Hst.
    destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
    apply andb_prop in Hpins as [Hqs Hnv].
    apply instr_eqb_spec in Hqs.
    destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
    apply negb_true_iff in Hnv.
    assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
    { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
    split.
    - exists (lift cs). split.
      + rewrite <- lift_c0. apply csteps_lift. exact Ecs.
      + rewrite cinstr_lift. exact Hqs.
    - intros m Hm (c & Hc & Hcq).
      destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
      assert (Hccq : cinstr cc = tg).
      { rewrite <- cinstr_lift, Hlift. exact Hcq. }
      destruct (le_lt_dec m t) as [Hle | Hgt].
      + replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
        rewrite csteps_add, Ecs1' in Hcc.
        rewrite (cfires_complete tm (t - s) cs1 tg (m - s - 1) cc)
          in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
      + replace m with (t + (m - t)) in Hcc by lia.
        rewrite csteps_add, Ect in Hcc.
        apply csteps_lift in Hcc.
        destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [_ Hqfree].
        apply (Hqfree (lift cc)); [exact Hcc|].
        rewrite cinstr_lift, Hccq.
        apply in_map_iff. exists (tg, s). split; [reflexivity | exact Hin]. }
  assert (HNonHalt : NonHalt tm).
  { intros m HN.
    destruct (le_lt_dec m t) as [Hle | Hgt].
    + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
      apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
    + replace m with (t + (m - t)) in HN by lia.
      rewrite stepn_add, Hstept in HN.
      destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [Heq _].
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
    { destruct (wrap_trs_agree tm W (lift ct) Him (s'' - t)) as [Heq _].
      transitivity (stepn tm (s'' - t) (lift ct)); [exact Heq | exact Hcw]. }
    assert (Happ : appears_tr cconf cinstr Sl tg'' = true).
    { rewrite <- Hccq.
      apply (live_fired_appears_tr tmw cconf cconf_enc cinstr
               (ng_succs tmw lset rset) (ng_covers n lset rset)
               cconf_enc_inj CST SS
               Sl (ng_start n ct) (lift ct) Hclb Hmem Hcov0
               (s'' - t) (lift cc) Hwrun). }
    destruct (live_appears_recur_lex_tr tmw cconf cconf_enc cinstr
                (ng_succs tmw lset rset) (ng_covers n lset rset)
                cconf_enc_inj CST SS
                Sl (fun tg' => map (ng_comp_denote tmw n) (cert tg'))
                (ng_start n ct) ct tg''
                Hclb (Hexd tg'') Hlive Hmem Hcov0 Happ
                (S s'' - t)) as (k & c' & Hk & Hstepk & Hqk).
    assert (Hstm : stepn tm k (lift ct) = Some c').
    { destruct (wrap_trs_agree tm W (lift ct) Him k) as [Heqk _].
      rewrite <- Heqk. exact Hstepk. }
    apply (Hlast'' (t + k)); [lia|].
    exists c'. split; [| exact Hqk].
    rewrite stepn_add, Hstept. exact Hstm.
  - destruct tgs as [| [tg s] rest]; [simpl in Hlen; lia|].
    destruct (Hpinned tg s (or_introl eq_refl)) as [Hf Hq].
    eapply quiet_after_tr_qh. split; [exact Hf | exact Hq].
Qed.

(** ** The wrap argument, generic in the abstract domain

    [ngram_check_qhboundtr_lex_sound]'s wrap-lifting glue touches the
    n-gram domain only through ClosureTr's target-generic lemmas, so
    the same argument works over ANY abstract domain whose successor
    relation simulates the WRAPPED machine.  Built for the RepWL
    instantiation (CensusTr/RepWLTr): an instruction pin [(q, s)] is a
    TAPE-VALUE exclusion -- state [q] stays busy on the sibling symbol
    -- and the n-gram window refill manufactures the pinned instruction
    inside the wrapped closure on 76% of the measured v4 suspects,
    while RepWL's run-length blocks close 81.8% of them at their first
    rung (SCOPING_INSTR.md 7.1m). *)

Section WrapGeneric.

  Variable tm : TM.
  Variable tgs : list (Instr * nat).
  Variable t : nat.

  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_instr : A -> Instr.
  Variable succs : A -> option (list A).
  Variable covers : A -> ExecState -> Prop.

  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_instr : forall a c, covers a c -> a_instr a = instr_of c.
  (** [succs] simulates the WRAPPED machine *)
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step (tm_wrap_trs tm (map fst tgs)) c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  Definition wrap_check_qhboundtr_g (fuel : nat) (a0 : A)
      (cert : Instr -> list (lexcomp A)) : bool :=
    (1 <=? length tgs) &&
    forallb (wrap_pin_ok tm t) tgs &&
    match csteps tm t c0 with
    | Some _ =>
        match close_tr A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            closed_tr_b A a_enc succs Sl &&
            mem_tr A a_enc a0 Sl &&
            live_lex_ok_tr A a_enc a_instr succs Sl cert
        | None => false
        end
    | None => false
    end.

  Theorem wrap_check_qhboundtr_g_sound : forall fuel a0 cert,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall tg0,
       Forall (comp_exact (tm_wrap_trs tm (map fst tgs)) A succs covers)
              (cert tg0)) ->
    wrap_check_qhboundtr_g fuel a0 cert = true ->
    NonHalt tm
    /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
    /\ QuasiHaltsTr tm.
  Proof.
    intros fuel a0 cert Hcov0A Hexd H.
    unfold wrap_check_qhboundtr_g in H.
    apply andb_prop in H as [H Hcl].
    apply andb_prop in H as [Hlen Hpins].
    apply Nat.leb_le in Hlen.
    destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
    destruct (close_tr A a_enc succs fuel [] PositiveSet.empty [a0])
      as [Sl|] eqn:Ecl; [|discriminate].
    apply andb_prop in Hcl as [Hwc Hlive].
    apply andb_prop in Hwc as [Hclb Hmem].
    apply mem_In_tr in Hmem; [|exact a_enc_inj].
    pose proof (Hcov0A ct eq_refl) as Hcov0.
    set (W := map fst tgs) in *.
    set (tmw := tm_wrap_trs tm W) in *.
    assert (Him : forall k, stepn tmw k (lift ct) <> None).
    { intros k HN.
      destruct (closure_invariant_tr tmw A a_enc succs covers
                  a_enc_inj succs_sound Sl Hclb a0 (lift ct) Hmem Hcov0 k)
        as (c' & a' & Hst' & _ & _).
      congruence. }
    assert (Hstept : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
    rewrite forallb_forall in Hpins.
    assert (Hpinned : forall tg s, In (tg, s) tgs ->
      FiresAt tm tg s /\ (forall m, s < m -> ~ FiresAt tm tg m)).
    { intros tg s Hin.
      specialize (Hpins (tg, s) Hin).
      unfold wrap_pin_ok in Hpins.
      apply andb_prop in Hpins as [Hst Hpins].
      apply Nat.ltb_lt in Hst.
      destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
      apply andb_prop in Hpins as [Hqs Hnv].
      apply instr_eqb_spec in Hqs.
      destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
      apply negb_true_iff in Hnv.
      assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
      { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
      split.
      - exists (lift cs). split.
        + rewrite <- lift_c0. apply csteps_lift. exact Ecs.
        + rewrite cinstr_lift. exact Hqs.
      - intros m Hm (c & Hc & Hcq).
        destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
        assert (Hccq : cinstr cc = tg).
        { rewrite <- cinstr_lift, Hlift. exact Hcq. }
        destruct (le_lt_dec m t) as [Hle | Hgt].
        + replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
          rewrite csteps_add, Ecs1' in Hcc.
          rewrite (cfires_complete tm (t - s) cs1 tg (m - s - 1) cc)
            in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
        + replace m with (t + (m - t)) in Hcc by lia.
          rewrite csteps_add, Ect in Hcc.
          apply csteps_lift in Hcc.
          destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [_ Hqfree].
          apply (Hqfree (lift cc)); [exact Hcc|].
          rewrite cinstr_lift, Hccq.
          apply in_map_iff. exists (tg, s).
          split; [reflexivity | exact Hin]. }
    assert (HNonHalt : NonHalt tm).
    { intros m HN.
      destruct (le_lt_dec m t) as [Hle | Hgt].
      + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
        apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
      + replace m with (t + (m - t)) in HN by lia.
        rewrite stepn_add, Hstept in HN.
        destruct (wrap_trs_agree tm W (lift ct) Him (m - t)) as [Heq _].
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
      { destruct (wrap_trs_agree tm W (lift ct) Him (s'' - t)) as [Heq _].
        transitivity (stepn tm (s'' - t) (lift ct));
          [exact Heq | exact Hcw]. }
      assert (Happ : appears_tr A a_instr Sl tg'' = true).
      { rewrite <- Hccq.
        apply (live_fired_appears_tr tmw A a_enc a_instr succs covers
                 a_enc_inj covers_instr succs_sound
                 Sl a0 (lift ct) Hclb Hmem Hcov0
                 (s'' - t) (lift cc) Hwrun). }
      destruct (live_appears_recur_lex_tr tmw A a_enc a_instr succs covers
                  a_enc_inj covers_instr succs_sound
                  Sl cert a0 ct tg''
                  Hclb (Hexd tg'') Hlive Hmem Hcov0 Happ
                  (S s'' - t)) as (k & c' & Hk & Hstepk & Hqk).
      assert (Hstm : stepn tm k (lift ct) = Some c').
      { destruct (wrap_trs_agree tm W (lift ct) Him k) as [Heqk _].
        rewrite <- Heqk. exact Hstepk. }
      apply (Hlast'' (t + k)); [lia|].
      exists c'. split; [| exact Hqk].
      rewrite stepn_add, Hstept. exact Hstm.
    - destruct tgs as [| [tg s] rest]; [simpl in Hlen; lia|].
      destruct (Hpinned tg s (or_introl eq_refl)) as [Hf Hq].
      eapply quiet_after_tr_qh. split; [exact Hf | exact Hq].
  Qed.

End WrapGeneric.
