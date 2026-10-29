(** Non-injective alphabet quotients preserve states, not instruction identities.
    No instruction bound is exported by this module. *)
From Coq Require Import Arith Lia Bool List NArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Closeout Pipeline
  StateOnlyCloseout AlphabetReduction Alphabet23 AlphabetMask.
Import ListNotations.

Definition quotient_trans (f : Sym -> S.Sym) (tr : Trans) : S.Trans :=
  S.mkTrans (f (t_write tr)) (down_dir (t_dir tr)) (up_state (t_next tr)).
Definition quotient_machine (f : Sym -> S.Sym) (representative : S.Sym -> Sym) (tm : TM) : S.TM :=
  fun q a => match q with
  | S.StA => option_map (quotient_trans f) (tm StA (representative a))
  | S.StB => option_map (quotient_trans f) (tm StB (representative a))
  | S.StC => None end.
Definition QuotientCompatible f representative (tm : TM) : Prop := forall q a,
  option_map (quotient_trans f) (tm q a) =
  option_map (quotient_trans f) (tm q (representative (f a))).
Definition quotient_tape f (tp : Tape) : S.Tape :=
  S.mkTape (fun n => f (t_left tp n)) (f (t_head tp)) (fun n => f (t_right tp n)).
Definition quotient_config f (c : ExecState) : S.ExecState :=
  (up_state (fst c), quotient_tape f (snd c)).
Lemma quotient_move : forall f d w tp,
  quotient_tape f (tape_move d w tp) =
  S.tape_move (down_dir d) (f w) (quotient_tape f tp).
Proof.
  intros f d w [l h r]; destruct d;
    unfold tape_move,down_dir,S.tape_move,quotient_tape; cbn; f_equal;
    apply functional_extensionality; intros [|n]; reflexivity.
Qed.
Lemma quotient_step : forall f representative tm c,
  QuotientCompatible f representative tm ->
  option_map (quotient_config f) (step tm c) =
  S.step (quotient_machine f representative tm) (quotient_config f c).
Proof.
  intros f representative tm [q tp] H.
  unfold step,S.step,quotient_config,quotient_machine; cbn.
  destruct q; cbn; rewrite <- (H _ (t_head tp));
    destruct (tm _ _) as [tr|]; cbn; try reflexivity;
    unfold quotient_config; cbn; now rewrite quotient_move.
Qed.
Lemma quotient_steps : forall f representative tm n c,
  QuotientCompatible f representative tm ->
  option_map (quotient_config f) (stepn tm n c) =
  S.stepn (quotient_machine f representative tm) n (quotient_config f c).
Proof.
  intros f representative tm n; induction n as [|n IH]; intros c H; [reflexivity|].
  change (option_map (quotient_config f)
    (match step tm c with Some d => stepn tm n d | None => None end) =
    match S.step (quotient_machine f representative tm) (quotient_config f c) with
    | Some d => S.stepn (quotient_machine f representative tm) n d | None => None end).
  rewrite <- (quotient_step f representative tm c H).
  destruct (step tm c); [apply IH; exact H|reflexivity].
Qed.
Lemma quotient_initial : forall f, f S0 = S.S0 -> quotient_config f InitES = S.InitES.
Proof. intros f H. unfold quotient_config, InitES,quotient_tape,blank_side; cbn. now rewrite H. Qed.
Lemma quotient_run : forall f representative tm n,
  f S0 = S.S0 -> QuotientCompatible f representative tm ->
  option_map (quotient_config f) (stepn tm n InitES) =
  S.stepn (quotient_machine f representative tm) n S.InitES.
Proof.
  intros f representative tm n H0 H.
  rewrite (quotient_steps f representative tm n InitES H), (quotient_initial f H0).
  reflexivity.
Qed.
Lemma quotient_admissible : forall f representative tm,
  SmallBB.Size.Admissible 2 3 (quotient_machine f representative tm).
Proof.
  intros f representative tm; split.
  - intros q a tr H. destruct q; cbn in H; try discriminate;
      destruct (tm _ _) as [[w d next]|] eqn:E; cbn in H; try discriminate;
      inversion H; subst; unfold SmallBB.Size.output_ok; cbn;
      destruct (f w), next; cbn; lia.
  - intros q a H. destruct q,a; cbn in *; try reflexivity; destruct H; lia.
Qed.
Lemma quotient_visits : forall f representative tm q n,
  f S0 = S.S0 -> QuotientCompatible f representative tm ->
  (VisitsAt tm q n <-> S.VisitsAt (quotient_machine f representative tm) (up_state q) n).
Proof.
  intros f representative tm q n H0 H.
  pose proof (quotient_run f representative tm n H0 H) as E.
  split; intros [c [Ec Hq]].
  - rewrite Ec in E. exists (quotient_config f c); split; [symmetry; exact E|].
    unfold quotient_config; cbn; now rewrite Hq.
  - destruct (stepn tm n InitES) as [d|] eqn:Ed; [|cbn in E; congruence].
    cbn in E. rewrite Ec in E. inversion E; subst c.
    exists d; split; [exact Ed|]. now apply up_state_injective.
Qed.
Theorem quotient_state_bound : forall f representative tm,
  f S0 = S.S0 -> QuotientCompatible f representative tm -> QHBound 59 tm.
Proof.
  intros f representative tm H0 H q n [Hv Hquiet].
  pose proof (proj1 (small23_bounds _ (quotient_admissible f representative tm))) as Hb.
  apply (Hb (up_state q) n). split.
  - now apply (quotient_visits f representative tm q n H0 H).
  - intros k Hk Hv'. apply (Hquiet k Hk).
    now apply (quotient_visits f representative tm q k H0 H).
Qed.
Lemma quotient_survival_nonhalt : forall f representative tm c,
  f S0 = S.S0 -> QuotientCompatible f representative tm ->
  stepn tm 67 InitES = Some c -> NonHalt tm.
Proof.
  intros f representative tm c H0 H E.
  assert (Hsmall : S.NonHalt (quotient_machine f representative tm)).
  { eapply small_bound_survival.
    - exact (proj2 (small23_bounds _ (quotient_admissible f representative tm))).
    - rewrite <- (quotient_run f representative tm 67 H0 H), E. reflexivity. }
  intros n Enone. apply (Hsmall n).
  rewrite <- (quotient_run f representative tm n H0 H), Enone. reflexivity.
Qed.

Definition quotient_projection (labels : list nat) a : S.Sym :=
  match nth (sym_index a) labels 0 with 0 => S.S0 | 1 => S.S1 | _ => S.S2 end.
Definition quotient_representative labels a :=
  match find (fun x => S.sym_eqb (quotient_projection labels x) a) closeout_symbols with
  | Some x => x | None => S0 end.
Definition small_trans_eqb (a b : S.Trans) :=
  S.sym_eqb (S.t_write a) (S.t_write b) &&
  (match S.t_dir a,S.t_dir b with S.DL,S.DL | S.DR,S.DR => true | _,_ => false end) &&
  S.st_eqb (S.t_next a) (S.t_next b).
Lemma small_trans_eqb_sound : forall a b, small_trans_eqb a b = true -> a = b.
Proof. intros [w d q] [w' d' q']; destruct w,d,q,w',d',q'; cbn; congruence. Qed.
Definition small_cell_eqb (a b : option S.Trans) :=
  match a,b with None,None => true | Some x,Some y => small_trans_eqb x y | _,_ => false end.
Lemma small_cell_eqb_sound : forall a b, small_cell_eqb a b = true -> a = b.
Proof.
  intros [a|] [b|]; cbn; try discriminate; [intro H; apply small_trans_eqb_sound in H; congruence|reflexivity].
Qed.
Definition quotient_tables_check labels tm :=
  forallb (fun q => forallb (fun a => small_cell_eqb
    (option_map (quotient_trans (quotient_projection labels)) (tm q a))
    (option_map (quotient_trans (quotient_projection labels))
      (tm q (quotient_representative labels (quotient_projection labels a))))) closeout_symbols) all_St.
Lemma quotient_tables_check_sound : forall labels tm,
  quotient_tables_check labels tm = true ->
  QuotientCompatible (quotient_projection labels) (quotient_representative labels) tm.
Proof.
  intros labels tm H q a. unfold quotient_tables_check in H.
  apply forallb_forall with (x:=q) in H; [|apply all_St_complete].
  apply forallb_forall with (x:=a) in H; [apply small_cell_eqb_sound; exact H|apply closeout_symbols_complete].
Qed.
Definition state_quotient_check labels tm :=
  (Nat.eqb (length labels) 4 && forallb (fun x => x <? 3) labels) &&
  S.sym_eqb (quotient_projection labels S0) S.S0 &&
  quotient_tables_check labels tm &&
  match stepn tm 67 InitES with Some _ => true | None => false end.
Theorem state_quotient_check_sound : forall labels tm,
  state_quotient_check labels tm = true -> NonHalt tm /\ QHBound 59 tm.
Proof.
  intros labels tm H. unfold state_quotient_check in H.
  apply andb_prop in H as [H Hrun]. apply andb_prop in H as [H Htable].
  apply andb_prop in H as [_ Hblank]. apply S.sym_eqb_spec in Hblank.
  apply quotient_tables_check_sound in Htable.
  split.
  - destruct (stepn tm 67 InitES) as [c|] eqn:E; [|discriminate].
    eapply quotient_survival_nonhalt; eauto.
  - eapply quotient_state_bound; eauto.
Qed.

Definition StateQuotientRows := list (list nat * list nat).
Definition state_quotient_batch_check (rows : StateQuotientRows) :=
  forallb (fun row => state_quotient_check (snd row) (machine_of_codes (fst row))) rows.
Definition state_quotient_board (rows : StateQuotientRows) :=
  map (fun row => machine_of_codes (fst row)) rows.
Lemma state_quotient_board_small_sound : forall rows,
  state_quotient_batch_check rows = true -> StateBoardSound 59 (state_quotient_board rows).
Proof.
  intros rows H family Hin tm Hle. apply in_map_iff in Hin as [row [<- Hin]].
  unfold state_quotient_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  destruct (state_quotient_check_sound _ _ H) as [Hnh Hb].
  exact (state_bound_extend 59 _ _ Hnh Hb Hle).
Qed.
Lemma state_quotient_board_sound : forall rows,
  state_quotient_batch_check rows = true -> StateBoardSound score (state_quotient_board rows).
Proof.
  intros rows H family Hin tm Hle q n Hq.
  pose proof (state_quotient_board_small_sound rows H family Hin tm Hle q n Hq) as Hb.
  assert (Hbig : (59 <= scoreN)%N) by (vm_compute; discriminate).
  unfold score; lia.
Qed.
Lemma state_quotient_board_nonhalt : forall rows,
  state_quotient_batch_check rows = true ->
  forall family, In family (state_quotient_board rows) -> NonHalt family.
Proof.
  intros rows H family Hin. apply in_map_iff in Hin as [row [<- Hin]].
  unfold state_quotient_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  exact (proj1 (state_quotient_check_sound _ _ H)).
Qed.

Example incompatible_merge_rejected :
  state_quotient_check [0;0;1;2] (machine_of_codes [5;0;0;0;0;0;0;0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example shifted_blank_rejected :
  state_quotient_check [1;0;1;2] (machine_of_codes [0;0;0;0;0;0;0;0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example quotient_halt_rejected : state_quotient_check [0;1;2;2] empty = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_class_rejected :
  state_quotient_check [0;1;2;3] (machine_of_codes [0;0;0;0;0;0;0;0]) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions state_quotient_check_sound.
