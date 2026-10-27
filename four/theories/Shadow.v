(** One blank step followed by a state swap.  A core bound B gives B+1 for
    the original machine.  The checked table relation covers all completions
    of the original partial table, provided the core certificate is nonhalting. *)
From Coq Require Import Arith Lia List Bool NArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Mirror CycleCensus Symmetry Closeout.
Import ListNotations.

Definition swap_state q := match q with StA => StB | StB => StA end.
Definition swap_config (c : ExecState) : ExecState := (swap_state (fst c), snd c).
Definition swap_instr (tg : Instr) : Instr := (swap_state (fst tg), snd tg).
Definition swap_tm (tm : TM) : TM := fun q s =>
  match tm (swap_state q) s with
  | None => None
  | Some tr => Some (mkTrans (t_write tr) (t_dir tr) (swap_state (t_next tr)))
  end.
Lemma swap_state_involutive : forall q, swap_state (swap_state q)=q.
Proof. destruct q; reflexivity. Qed.
Lemma swap_instr_involutive : forall tg, swap_instr (swap_instr tg)=tg.
Proof. intros [q s]; unfold swap_instr; cbn; now rewrite swap_state_involutive. Qed.
Lemma swap_config_instr : forall c, instr_of (swap_config c)=swap_instr (instr_of c).
Proof. reflexivity. Qed.
Lemma swap_step : forall tm c,
  step tm (swap_config c)=option_map swap_config (step (swap_tm tm) c).
Proof.
  intros tm [q tp]. unfold step,swap_config,swap_tm; cbn.
  destruct (tm (swap_state q) (t_head tp)) as [[w d q']|]; cbn; [|reflexivity].
  now rewrite swap_state_involutive.
Qed.
Lemma swap_stepn : forall tm n c,
  stepn tm n (swap_config c)=option_map swap_config (stepn (swap_tm tm) n c).
Proof.
  intros tm n; induction n; intro c; cbn [stepn]; [reflexivity|].
  rewrite swap_step. destruct (step (swap_tm tm) c); cbn; [apply IHn|reflexivity].
Qed.
Lemma move_blank : forall d,
  tape_move d S0 (snd InitES)=snd InitES.
Proof.
  destruct d; unfold InitES,tape_move,blank_side,push_side,tail_side; cbn;
    f_equal; apply functional_extensionality; intros [|n]; reflexivity.
Qed.

Section BlankStep.
Variable tm : TM.
Variable d : Dir.
Hypothesis first_blank : tm StA S0=Some (mkTrans S0 d StB).

Lemma blank_shadow_run : forall n,
  stepn tm (S n) InitES=option_map swap_config (stepn (swap_tm tm) n InitES).
Proof.
  intro n. cbn [stepn]. unfold step at 1; cbn [InitES fst snd t_head].
  rewrite first_blank; cbn [t_next t_dir t_write].
  change (stepn tm n (StB,tape_move d S0 (snd InitES)) =
    option_map swap_config (stepn (swap_tm tm) n InitES)).
  rewrite move_blank. exact (swap_stepn tm n InitES).
Qed.
Lemma blank_shadow_visits : forall q n,
  VisitsAt tm (swap_state q) (S n) <-> VisitsAt (swap_tm tm) q n.
Proof.
  intros q n; unfold VisitsAt. rewrite blank_shadow_run.
  destruct (stepn (swap_tm tm) n InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); injection Hc as E; subst c'.
    + exists c; split; [reflexivity|].
      change (swap_state (fst c)=swap_state q) in Hq.
      apply (f_equal swap_state) in Hq. now rewrite !swap_state_involutive in Hq.
    + exists (swap_config c); split; [reflexivity|]. cbn [swap_config fst]. now rewrite Hq.
  - split; intros (c & Hc & _); discriminate.
Qed.
Lemma blank_shadow_fires : forall tg n,
  FiresAt tm (swap_instr tg) (S n) <-> FiresAt (swap_tm tm) tg n.
Proof.
  intros tg n; unfold FiresAt. rewrite blank_shadow_run.
  destruct (stepn (swap_tm tm) n InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); injection Hc as E; subst c'.
    + exists c; split; [reflexivity|]. rewrite swap_config_instr in Hq.
      apply (f_equal swap_instr) in Hq. now rewrite !swap_instr_involutive in Hq.
    + exists (swap_config c); split; [reflexivity|]. now rewrite swap_config_instr,Hq.
  - split; intros (c & Hc & _); discriminate.
Qed.
Lemma blank_shadow_nonhalt : NonHalt (swap_tm tm) -> NonHalt tm.
Proof.
  intros H [|n]; [discriminate|]. rewrite blank_shadow_run.
  specialize (H n). destruct (stepn (swap_tm tm) n InitES); cbn; congruence.
Qed.
Lemma blank_shadow_quiet : forall q n,
  QuietAfter tm (swap_state q) (S n) <-> QuietAfter (swap_tm tm) q n.
Proof.
  intros q n; unfold QuietAfter; split; intros [Hv Hq]; split.
  - now apply blank_shadow_visits in Hv.
  - intros k Hk Hvk. apply (Hq (S k)); [lia|]. now apply blank_shadow_visits.
  - now apply blank_shadow_visits.
  - intros [|k] Hk Hvk; [lia|]. apply (Hq k); [lia|]. now apply blank_shadow_visits in Hvk.
Qed.
Lemma blank_shadow_quiet_tr : forall tg n,
  QuietAfterTr tm (swap_instr tg) (S n) <-> QuietAfterTr (swap_tm tm) tg n.
Proof.
  intros tg n; unfold QuietAfterTr; split; intros [Hv Hq]; split.
  - now apply blank_shadow_fires in Hv.
  - intros k Hk Hvk. apply (Hq (S k)); [lia|]. now apply blank_shadow_fires.
  - now apply blank_shadow_fires.
  - intros [|k] Hk Hvk; [lia|]. apply (Hq k); [lia|]. now apply blank_shadow_fires in Hvk.
Qed.
Theorem blank_shadow_bounds : forall bs bi,
  Bounds bs bi (swap_tm tm) -> Bounds (N.succ bs) (N.succ bi) tm.
Proof.
  intros bs bi [Hs Hi]; split; intros tg [|n] Hq; rewrite N2Nat.inj_succ; [lia| |lia|].
  - assert (Hcore : QuietAfter (swap_tm tm) (swap_state tg) n).
    { apply blank_shadow_quiet. now rewrite swap_state_involutive. }
    specialize (Hs _ _ Hcore). lia.
  - assert (Hcore : QuietAfterTr (swap_tm tm) (swap_instr tg) n).
    { apply blank_shadow_quiet_tr. now rewrite swap_instr_involutive. }
    specialize (Hi _ _ Hcore). lia.
Qed.
End BlankStep.

Definition shadow_transform p (mirrored : bool) tm :=
  let renamed := perm_tm p (swap_tm tm) in
  if mirrored then mirror_tm renamed else renamed.

Theorem shadow_core_bounds : forall tm core p mirrored d bs bi,
  tm StA S0=Some (mkTrans S0 d StB) ->
  TM_le core (shadow_transform p mirrored tm) ->
  NonHalt core -> Bounds bs bi core ->
  NonHalt tm /\ Bounds (N.succ bs) (N.succ bi) tm.
Proof.
  intros tm core p mirrored d bs bi Hfirst Hle Hnh Hb.
  assert (Hrun : NonHalt (shadow_transform p mirrored tm)).
  { intros n E. rewrite (extend_run core _ Hnh Hle n) in E. exact (Hnh n E). }
  pose proof (extend_bounds bs bi core _ Hnh Hb Hle) as Hbounds.
  unfold shadow_transform in Hrun,Hbounds. destruct mirrored.
  - apply mirror_nonhalt in Hrun. apply mirror_bounds in Hbounds.
    apply perm_nonhalt in Hrun. apply perm_bounds in Hbounds.
    split; [eapply blank_shadow_nonhalt|eapply blank_shadow_bounds]; eauto.
  - apply perm_nonhalt in Hrun. apply perm_bounds in Hbounds.
    split; [eapply blank_shadow_nonhalt|eapply blank_shadow_bounds]; eauto.
Qed.

Definition shadow_check tm core p mirrored :=
  match tm StA S0 with
  | Some (mkTrans S0 _ StB) => table_leb core (shadow_transform p mirrored tm)
  | _ => false
  end.
Theorem shadow_check_sound : forall tm core p mirrored bs bi,
  shadow_check tm core p mirrored=true -> NonHalt core -> Bounds bs bi core ->
  forall complete, TM_le tm complete ->
  NonHalt complete /\ Bounds (N.succ bs) (N.succ bi) complete.
Proof.
  intros tm core p mirrored bs bi H Hnh Hb complete Hle.
  unfold shadow_check in H.
  destruct (tm StA S0) as [[s d q]|] eqn:E; [|discriminate].
  destruct s,q; try discriminate.
  apply table_leb_spec in H.
  destruct (shadow_core_bounds tm core p mirrored d bs bi E H Hnh Hb) as [Hn Hbound].
  split.
  - intros n Hnone. rewrite (extend_run tm complete Hn Hle n) in Hnone. exact (Hn n Hnone).
  - eapply extend_bounds; eauto.
Qed.
