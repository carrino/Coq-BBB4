(** A three-symbol projection may halt at the first forbidden write.  If it
    survives the proved BBB23 bound, that halt can never occur. *)
From Coq Require Import Arith Lia Bool List NArith.
From SmallBB Require Import Statement StatementTr Bounds.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Closeout
  AlphabetReduction Alphabet23 Pipeline.
Import ListNotations.

Definition active_symbolb (b : bool) (a : Sym) := negb (sym_eqb a (if b then S2 else S3)).
Lemma active_symbolb_spec : forall b a,
  active_symbolb b a = true <-> active_symbol b a.
Proof.
  intros b a. unfold active_symbolb, active_symbol.
  rewrite Bool.negb_true_iff. destruct (sym_eqb a (if b then S2 else S3)) eqn:E.
  - apply sym_eqb_spec in E. split; [discriminate|congruence].
  - split; [|reflexivity]. intros _ Heq. apply sym_eqb_spec in Heq; congruence.
Qed.
Definition mask_alphabet b (tm : TM) : TM := fun q a =>
  if active_symbolb b a then
    match tm q a with
    | None => None
    | Some tr => if active_symbolb b (t_write tr) then Some tr else None
    end
  else None.
Definition SafeAlphabet b (tm : TM) :=
  forall q a tr, active_symbol b a -> tm q a = Some tr -> active_symbol b (t_write tr).
Lemma mask_safe : forall b tm, SafeAlphabet b (mask_alphabet b tm).
Proof.
  intros b tm q a tr Ha E. unfold mask_alphabet in E.
  destruct (active_symbolb b a); [|discriminate].
  destruct (tm q a) as [tr'|]; [|discriminate].
  destruct (active_symbolb b (t_write tr')) eqn:Ew; [|discriminate].
  inversion E; subst tr'. now apply active_symbolb_spec.
Qed.
Lemma mask_extends : forall b tm, TM_le (mask_alphabet b tm) tm.
Proof.
  intros b tm q a. unfold mask_alphabet.
  destruct (active_symbolb b a); [|left; reflexivity].
  destruct (tm q a) as [tr|]; [|left; reflexivity].
  destruct (active_symbolb b (t_write tr)); [right|left]; reflexivity.
Qed.
Lemma safe_step_active : forall b tm c d,
  SafeAlphabet b tm -> active_tape b (snd c) -> step tm c = Some d ->
  active_tape b (snd d).
Proof.
  intros b tm [q tp] d Hsafe Htp E. unfold step in E.
  destruct (tm q (t_head tp)) as [tr|] eqn:Et; [|discriminate].
  inversion E; subst d. cbn. apply active_move; [exact Htp|].
  eapply Hsafe; [exact (proj1 Htp)|exact Et].
Qed.
Lemma safe_project_steps : forall b tm n c,
  SafeAlphabet b tm -> active_tape b (snd c) ->
  option_map down_config (stepn tm n c) =
  S.stepn (reduced_machine b tm) n (down_config c).
Proof.
  intros b tm n; induction n as [|n IH]; intros c Hsafe Hc; [reflexivity|].
  change (option_map down_config
    (match step tm c with Some d => stepn tm n d | None => None end) =
    match S.step (reduced_machine b tm) (down_config c) with
    | Some d => S.stepn (reduced_machine b tm) n d | None => None end).
  rewrite <- (reduced_step b tm c Hc).
  destruct (step tm c) as [d|] eqn:E; [|reflexivity]. cbn [option_map].
  apply IH; [exact Hsafe|]. eapply safe_step_active; eauto.
Qed.

(** A finite quasihalting bound is also a halting-time bound.  Survival at
    [bound], not merely [bound-1], therefore proves nonhalting. *)
Lemma small_bound_survival : forall tm bound c,
  SmallBB.Bounds.QHBoundTr bound tm ->
  S.stepn tm bound S.InitES = Some c -> S.NonHalt tm.
Proof.
  intros tm bound c Hb Hsurvive n; induction n as [|n IH]; [discriminate|].
  replace (S n) with (n+1) by lia. rewrite S.stepn_add.
  destruct (S.stepn tm n S.InitES) as [d|] eqn:Ed; [|contradiction].
  cbn [S.stepn]. destruct (S.step tm d) as [e|] eqn:Estep; [discriminate|].
  intros _.
  assert (Ehalt : S.stepn tm (S n) S.InitES = None).
  { replace (S n) with (n+1) by lia. rewrite S.stepn_add, Ed. cbn [S.stepn]. now rewrite Estep. }
  assert (Hquiet : ST.QuietAfterTr tm (ST.instr_of d) n).
  { split; [exists d; auto|]. intros k Hk [e [Ee _]].
    replace k with (S n + (k-S n)) in Ee by lia.
    rewrite S.stepn_add, Ehalt in Ee; discriminate. }
  pose proof (Hb _ _ Hquiet) as Hn.
  replace bound with (S n + (bound-S n)) in Hsurvive by lia.
  rewrite S.stepn_add, Ehalt in Hsurvive; discriminate.
Qed.
Definition alphabet_survival_check b tm :=
  match stepn (mask_alphabet b tm) 67 InitES with Some _ => true | None => false end.
Lemma mask_nonhalt : forall b tm,
  alphabet_survival_check b tm = true -> NonHalt (mask_alphabet b tm).
Proof.
  intros b tm H. unfold alphabet_survival_check in H.
  destruct (stepn (mask_alphabet b tm) 67 InitES) as [c|] eqn:E; [|discriminate].
  pose proof (safe_project_steps b (mask_alphabet b tm) 67 InitES
    (mask_safe b tm) (active_initial b)) as Es.
  rewrite E in Es. cbn [option_map] in Es.
  assert (Hsmall : S.NonHalt (reduced_machine b (mask_alphabet b tm))).
  { eapply small_bound_survival.
    - exact (proj2 (small23_bounds _ (reduced_admissible b (mask_alphabet b tm)))).
    - symmetry; exact Es. }
  intros n Enone. pose proof (safe_project_steps b (mask_alphabet b tm) n InitES
    (mask_safe b tm) (active_initial b)) as En.
  rewrite Enone in En. apply (Hsmall n). symmetry; exact En.
Qed.

Definition fill_alphabet b (tm : TM) : TM := fun q a =>
  if active_symbolb b a then
    match mask_alphabet b tm q a with
    | Some tr => Some tr | None => Some (mkTrans S0 DL StA)
    end
  else None.
Lemma fill_closed : forall b tm, ClosedAlphabet b (fill_alphabet b tm).
Proof.
  intros b tm q a Ha. unfold fill_alphabet.
  apply active_symbolb_spec in Ha. rewrite Ha.
  destruct (mask_alphabet b tm q a) as [tr|] eqn:E.
  - exists tr; split; [reflexivity|]. exact (mask_safe b tm q a tr (proj1 (active_symbolb_spec b a) Ha) E).
  - exists (mkTrans S0 DL StA); split; [reflexivity|]. destruct b; discriminate.
Qed.
Lemma mask_fill_extends : forall b tm, TM_le (mask_alphabet b tm) (fill_alphabet b tm).
Proof.
  intros b tm q a. unfold fill_alphabet.
  destruct (mask_alphabet b tm q a) as [tr|] eqn:E; [|left; reflexivity].
  right. assert (active_symbolb b a = true).
  { unfold mask_alphabet in E. destruct (active_symbolb b a); congruence. }
  now rewrite H.
Qed.
Lemma bounds_same_run : forall bs bi a b,
  (forall n, stepn a n InitES = stepn b n InitES) -> Bounds bs bi a -> Bounds bs bi b.
Proof.
  intros bs bi a b E [Hs Hi].
  assert (Hv : forall q n, VisitsAt a q n <-> VisitsAt b q n).
  { intros q n. unfold VisitsAt. rewrite E; tauto. }
  assert (Hf : forall tg n, FiresAt a tg n <-> FiresAt b tg n).
  { intros tg n. unfold FiresAt. rewrite E; tauto. }
  split.
  - intros q n [Hn Hquiet]. apply (Hs q n). split; [apply Hv; exact Hn|].
    intros k Hk Hvisit. apply (Hquiet k Hk). now apply Hv.
  - intros tg n [Hn Hquiet]. apply (Hi tg n). split; [apply Hf; exact Hn|].
    intros k Hk Hfire. apply (Hquiet k Hk). now apply Hf.
Qed.
Theorem alphabet_survival_sound : forall b tm,
  alphabet_survival_check b tm = true -> NonHalt tm /\ Bounds 59 67 tm.
Proof.
  intros b tm H. pose proof (mask_nonhalt b tm H) as Hnh.
  assert (Hmasked : Bounds 59 67 (mask_alphabet b tm)).
  { apply (bounds_same_run 59 67 (fill_alphabet b tm)).
    - exact (extend_run _ _ Hnh (mask_fill_extends b tm)).
    - apply (alphabet23_bounds b), fill_closed. }
  split.
  - intros n E. rewrite (extend_run _ _ Hnh (mask_extends b tm) n) in E.
    exact (Hnh n E).
  - exact (extend_bounds 59 67 _ _ Hnh Hmasked (mask_extends b tm)).
Qed.

Definition immediate_halt : S.TM := fun _ _ => None.
Example zero_steps_survive : S.stepn immediate_halt 0 S.InitES = Some S.InitES.
Proof. reflexivity. Qed.
Example one_step_does_not_survive : S.stepn immediate_halt 1 S.InitES = None.
Proof. reflexivity. Qed.
Example immediate_halt_has_bound_one : SmallBB.Bounds.QHBoundTr 1 immediate_halt.
Proof.
  intros tg n [[c [E _]] _]. destruct n; [lia|]. discriminate.
Qed.
Example insufficient_survival_is_rejected : alphabet_survival_check false empty = false.
Proof. vm_compute; reflexivity. Qed.

Definition mask_batch_check (rows : AlphabetRows) :=
  forallb (fun row => alphabet_survival_check (snd row) (machine_of_codes (fst row))) rows.
Definition mask_board := alphabet_board.
Lemma mask_board_small_sound : forall rows,
  mask_batch_check rows = true -> BoardSound 59 67 (mask_board rows).
Proof.
  intros rows H family Hin tm Hle. apply in_map_iff in Hin as [row [<- Hin]].
  unfold mask_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  destruct (alphabet_survival_sound (snd row) (machine_of_codes (fst row)) H) as [Hnh Hb].
  exact (extend_bounds 59 67 _ _ Hnh Hb Hle).
Qed.
Lemma mask_board_nonhalt : forall rows,
  mask_batch_check rows = true -> forall family, In family (mask_board rows) -> NonHalt family.
Proof.
  intros rows H family Hin. apply in_map_iff in Hin as [row [<- Hin]].
  unfold mask_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  exact (proj1 (alphabet_survival_sound (snd row) (machine_of_codes (fst row)) H)).
Qed.
Lemma mask_board_sound : forall rows,
  mask_batch_check rows = true -> BoardSound scoreN scoreN (mask_board rows).
Proof.
  intros rows H family Hin tm Hle.
  apply (bounds_weaken 59 67 scoreN scoreN tm); try (vm_compute; discriminate).
  exact (mask_board_small_sound rows H family Hin tm Hle).
Qed.

Print Assumptions alphabet_survival_sound.
