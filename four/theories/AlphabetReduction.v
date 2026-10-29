(** A closed three-symbol alphabet inside a four-symbol machine.  The two
    unused table cells may be completed arbitrarily. *)
From Coq Require Import Arith Lia Bool List NArith FunctionalExtensionality.
From SmallBB Require Import Statement StatementTr Size Bounds.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Closeout.
Import ListNotations.
Module S := SmallBB.Statement.
Module ST := SmallBB.StatementTr.
Module SZ := SmallBB.Size.
Module SB := SmallBB.Bounds.

Definition up_state (q : St) : S.St :=
  match q with StA => S.StA | StB => S.StB end.
Definition up_symbol (third3 : bool) (s : S.Sym) : Sym :=
  match s with S.S0 => S0 | S.S1 => S1 | S.S2 => if third3 then S3 else S2 end.
Definition down_symbol (s : Sym) : S.Sym :=
  match s with S0 => S.S0 | S1 => S.S1 | S2 | S3 => S.S2 end.
Definition active_symbol (third3 : bool) (s : Sym) : Prop :=
  s <> if third3 then S2 else S3.
Definition down_dir (d : Dir) : S.Dir :=
  match d with DL => S.DL | DR => S.DR end.
Definition down_trans (tr : Trans) : S.Trans :=
  S.mkTrans (down_symbol (t_write tr)) (down_dir (t_dir tr)) (up_state (t_next tr)).
Definition reduced_machine (third3 : bool) (tm : TM) : S.TM := fun q a =>
  match q with
  | S.StA => option_map down_trans (tm StA (up_symbol third3 a))
  | S.StB => option_map down_trans (tm StB (up_symbol third3 a))
  | S.StC => None
  end.
Definition down_tape (tp : Tape) : S.Tape :=
  S.mkTape (fun n => down_symbol (t_left tp n)) (down_symbol (t_head tp))
    (fun n => down_symbol (t_right tp n)).
Definition down_config (c : ExecState) : S.ExecState :=
  (up_state (fst c), down_tape (snd c)).
Definition active_tape (third3 : bool) (tp : Tape) : Prop :=
  active_symbol third3 (t_head tp) /\
  (forall n, active_symbol third3 (t_left tp n)) /\
  (forall n, active_symbol third3 (t_right tp n)).
Definition ClosedAlphabet (third3 : bool) (tm : TM) : Prop :=
  forall q a, active_symbol third3 a ->
    exists tr, tm q a = Some tr /\ active_symbol third3 (t_write tr).

Lemma up_down_symbol : forall third3 a,
  active_symbol third3 a -> up_symbol third3 (down_symbol a) = a.
Proof. destruct third3, a; simpl; unfold active_symbol; simpl; congruence. Qed.
Lemma up_state_injective : forall q q', up_state q = up_state q' -> q = q'.
Proof. destruct q, q'; simpl; congruence. Qed.
Lemma active_symbol_injective : forall b a a',
  active_symbol b a -> active_symbol b a' ->
  down_symbol a = down_symbol a' -> a = a'.
Proof. intros b a a' Ha Ha' E. rewrite <- (up_down_symbol b a Ha),
  <- (up_down_symbol b a' Ha'). now rewrite E. Qed.

Lemma reduced_admissible : forall b tm, SZ.Admissible 2 3 (reduced_machine b tm).
Proof.
  intros b tm; split.
  - intros q a tr H. destruct q; cbn in H; try discriminate;
      destruct (tm _ _) as [[w d next]|] eqn:E; cbn in H; try discriminate;
      inversion H; subst; unfold SZ.output_ok; cbn;
      destruct w, next; cbn; lia.
  - intros q a H. destruct q, a; cbn in *; try reflexivity;
      destruct H; lia.
Qed.
Lemma active_initial : forall b, active_tape b (snd InitES).
Proof. destruct b; repeat split; intros; discriminate. Qed.
Lemma active_move : forall b tp d w,
  active_tape b tp -> active_symbol b w -> active_tape b (tape_move d w tp).
Proof.
  intros b [l h r] d w [Hh [Hl Hr]] Hw; destruct d; unfold active_tape; cbn.
  - split; [apply Hl|]. split; [intro n; apply Hl|]. intros [|n]; cbn; auto.
  - split; [apply Hr|]. split; [intros [|n]; cbn; auto|]. intro n; apply Hr.
Qed.
Lemma down_move : forall d w tp,
  down_tape (tape_move d w tp) =
  S.tape_move (down_dir d) (down_symbol w) (down_tape tp).
Proof. intros d w [l h r]; destruct d;
  unfold tape_move, down_dir, S.tape_move, down_tape; cbn; f_equal;
  apply functional_extensionality; intros [|n]; reflexivity. Qed.
Lemma reduced_step : forall b tm c,
  active_tape b (snd c) ->
  option_map down_config (step tm c) =
  S.step (reduced_machine b tm) (down_config c).
Proof.
  intros b tm [q tp] [Ha _]. destruct q;
    unfold step, S.step, down_config, reduced_machine; cbn;
    rewrite (up_down_symbol b (t_head tp) Ha);
    destruct (tm _ _) as [tr|]; cbn; try reflexivity;
    unfold down_config; cbn; now rewrite down_move.
Qed.
Lemma closed_step : forall b tm c,
  ClosedAlphabet b tm -> active_tape b (snd c) ->
  exists c', step tm c = Some c' /\ active_tape b (snd c').
Proof.
  intros b tm [q tp] Hclosed Htp.
  destruct (Hclosed q (t_head tp) (proj1 Htp)) as [tr [Htr Hw]].
  exists (t_next tr, tape_move (t_dir tr) (t_write tr) tp).
  split; [unfold step; now rewrite Htr|]. cbn. now apply active_move.
Qed.
Lemma closed_runs : forall b tm n c,
  ClosedAlphabet b tm -> active_tape b (snd c) ->
  exists c', stepn tm n c = Some c' /\ active_tape b (snd c') /\
    S.stepn (reduced_machine b tm) n (down_config c) = Some (down_config c').
Proof.
  intros b tm n; induction n as [|n IH]; intros c Hclosed Htp.
  - exists c; auto.
  - destruct (closed_step b tm c Hclosed Htp) as [d [Ed Hd]].
    destruct (IH d Hclosed Hd) as [e [Ee [He Es]]].
    exists e; split; [cbn; now rewrite Ed|]. split; [exact He|].
    change (match S.step (reduced_machine b tm) (down_config c) with
      | Some d => S.stepn (reduced_machine b tm) n d | None => None end = Some (down_config e)).
    rewrite <- (reduced_step b tm c Htp), Ed. exact Es.
Qed.
Lemma closed_nonhalt : forall b tm, ClosedAlphabet b tm -> NonHalt tm.
Proof.
  intros b tm H n. destruct (closed_runs b tm n InitES H (active_initial b))
    as [c [E _]]. rewrite E; discriminate.
Qed.
Lemma closed_visits : forall b tm q n,
  ClosedAlphabet b tm ->
  (VisitsAt tm q n <-> S.VisitsAt (reduced_machine b tm) (up_state q) n).
Proof.
  intros b tm q n H. destruct (closed_runs b tm n InitES H (active_initial b))
    as [c [E [Hc Es]]]. change (S.stepn (reduced_machine b tm) n S.InitES = Some (down_config c)) in Es.
  split; intros [d [Ed Hq]].
  - rewrite E in Ed; inversion Ed; subst d. exists (down_config c); split;
      [exact Es|]. unfold down_config; cbn; now rewrite Hq.
  - rewrite Es in Ed; inversion Ed; subst d. exists c; split; [exact E|].
    now apply up_state_injective.
Qed.
Lemma closed_fires : forall b tm q a n,
  ClosedAlphabet b tm -> active_symbol b a ->
  (FiresAt tm (q,a) n <->
    ST.FiresAt (reduced_machine b tm) (up_state q,down_symbol a) n).
Proof.
  intros b tm q a n H Ha.
  destruct (closed_runs b tm n InitES H (active_initial b)) as [c [E [Hc Es]]].
  change (S.stepn (reduced_machine b tm) n S.InitES = Some (down_config c)) in Es.
  split; intros [d [Ed Ht]].
  - rewrite E in Ed; inversion Ed; subst d. exists (down_config c); split;
      [exact Es|]. unfold instr_of in Ht. inversion Ht.
    unfold ST.instr_of, down_config; cbn. now rewrite H1, H2.
  - rewrite Es in Ed; inversion Ed; subst d. exists c; split; [exact E|].
    unfold ST.instr_of, down_config in Ht; cbn in Ht.
    inversion Ht as [[Hq Hs]]. unfold instr_of.
    apply up_state_injective in Hq.
    assert (t_head (snd c) = a) by (eapply active_symbol_injective; eauto; exact (proj1 Hc)).
    now rewrite Hq, H0.
Qed.
Lemma closed_fired_active : forall b tm q a n,
  ClosedAlphabet b tm -> FiresAt tm (q,a) n -> active_symbol b a.
Proof.
  intros b tm q a n H [c [E Ht]].
  destruct (closed_runs b tm n InitES H (active_initial b)) as [d [Ed [Hd _]]].
  rewrite E in Ed; inversion Ed; subst d.
  apply (f_equal snd) in Ht. cbn in Ht. rewrite <- Ht. exact (proj1 Hd).
Qed.
Theorem reduced_bounds : forall b tm bs bi,
  ClosedAlphabet b tm -> SB.Bounds bs bi (reduced_machine b tm) ->
  Bounds (N.of_nat bs) (N.of_nat bi) tm.
Proof.
  intros b tm bs bi H [Hs Hi]. unfold Bounds; rewrite !Nat2N.id; split.
  - intros q n [Hv Hquiet]. apply (Hs (up_state q) n). split.
    + now apply (closed_visits b tm q n H).
    + intros k Hk Hv'. apply (Hquiet k Hk). now apply (closed_visits b tm q k H).
  - intros [q a] n [Hf Hquiet].
    pose proof (closed_fired_active b tm q a n H Hf) as Ha.
    apply (Hi (up_state q, down_symbol a) n). split.
    + now apply (closed_fires b tm q a n H Ha).
    + intros k Hk Hf'. apply (Hquiet k Hk). now apply (closed_fires b tm q a k H Ha).
Qed.

Definition alphabet_check (b : bool) (tm : TM) : bool :=
  forallb (fun q => forallb (fun a =>
    match tm q (up_symbol b a) with
    | None => false
    | Some tr => negb (sym_eqb (t_write tr) (if b then S2 else S3))
    end) [S.S0; S.S1; S.S2]) [StA; StB].
Lemma alphabet_check_sound : forall b tm,
  alphabet_check b tm = true -> ClosedAlphabet b tm.
Proof.
  intros b tm H q a Ha. unfold alphabet_check in H.
  apply forallb_forall with (x:=q) in H; [|destruct q; cbn; auto].
  apply forallb_forall with (x:=down_symbol a) in H;
    [|destruct a; cbn; auto].
  rewrite (up_down_symbol b a Ha) in H.
  destruct (tm q a) as [tr|] eqn:E; [|discriminate].
  exists tr; split; [reflexivity|]. unfold active_symbol.
  apply Bool.negb_true_iff in H. intro Heq.
  apply sym_eqb_spec in Heq. congruence.
Qed.
Lemma closed_completion : forall b family tm,
  ClosedAlphabet b family -> TM_le family tm -> ClosedAlphabet b tm.
Proof.
  intros b family tm H Hle q a Ha. destruct (H q a Ha) as [tr [E Hw]].
  exists tr; split; [destruct (Hle q a) as [En|En]; congruence|exact Hw].
Qed.

Print Assumptions reduced_bounds.
