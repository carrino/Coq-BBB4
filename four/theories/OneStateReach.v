(** Uniform reachability through a one-state avoiding submachine.

    A rank on symbols decreases on every right-moving avoiding transition;
    left-moving writes may change it arbitrarily within [0,4]. The finite
    tape is read in radix10, with a head-position correction. Each avoiding
    interior step decreases this measure. Walking outside the represented
    finite tape reaches a blank, whose transition must enter the goal state.
    Reflection covers a rank decreasing on left-moving writes instead.

    This file proves STATE recurrence only. It makes no claim that all fired
    instructions recur. *)
From Coq Require Import Arith Lia Bool List Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Mirror TotalCompletion.
Import ListNotations.

Definition ore_symbols := [S0; S1; S2; S3].
Lemma ore_symbols_complete : forall s, In s ore_symbols.
Proof. destruct s; cbn; auto. Qed.

Fixpoint ore_left (rank : Sym -> nat) (l : list Sym) : nat :=
  match l with [] => 0 | x::t => rank x + 10 * ore_left rank t end.
Fixpoint ore_right (rank : Sym -> nat) (r : list Sym) : nat :=
  match r with [] => 0 | x::t => rank x * 10^length t + ore_right rank t end.
Definition ore_digits rank l h r :=
  10^(S (length r)) * ore_left rank l + rank h * 10^length r + ore_right rank r.
Definition ore_measure rank (cc : cconf) :=
  let '(_, (l,h,r)) := cc in
  2 * ore_digits rank l h r + 10^(length l + S (length r)) - 10^length r.

Lemma ore_power_pos : forall n, 0 < 10^n.
Proof. induction n; [cbn; lia|]. rewrite Nat.pow_succ_r'; nia. Qed.
Lemma ore_power_room : forall (l r : list Sym),
  10^length r <= 10^(length l + S (length r)).
Proof.
  intros l r. apply Nat.pow_le_mono_r; lia.
Qed.

Lemma ore_right_drop : forall rank q l h b r w,
  rank w < rank h ->
  ore_measure rank (q,(w::l,b,r)) < ore_measure rank (q,(l,h,b::r)).
Proof.
  intros rank q l h b r w Hrank.
  unfold ore_measure, ore_digits. cbn [length ore_left ore_right].
  replace (S (length l) + S (length r)) with (length l + S (S (length r))) by lia.
  assert (Hp := ore_power_pos (length r)).
  assert (Hroom := ore_power_room l (b::r)). cbn [length] in Hroom.
  rewrite !Nat.pow_succ_r' in *.
  nia.
Qed.

Lemma ore_left_drop : forall rank q l a h r w,
  rank w <= 4 ->
  ore_measure rank (q,(l,a,w::r)) < ore_measure rank (q,(a::l,h,r)).
Proof.
  intros rank q l a h r w Hw.
  unfold ore_measure, ore_digits. cbn [length ore_left ore_right].
  replace (S (length l) + S (length r)) with (length l + S (S (length r))) by lia.
  assert (Hp := ore_power_pos (length r)).
  assert (Hroom := ore_power_room l (w::r)). cbn [length] in Hroom.
  rewrite !Nat.pow_succ_r' in *.
  nia.
Qed.

Definition ore_reaches tm goal cc :=
  exists k cc', csteps tm k cc = Some cc' /\ fst cc' = goal.
Definition ore_cell_ok tm goal rank q h :=
  st_eqb q goal ||
  match tm q h with
  | None => false
  | Some tr => st_eqb (t_next tr) goal ||
      (negb (sym_eqb h S0) &&
       match t_dir tr with DL => true | DR => rank (t_write tr) <? rank h end)
  end.
Definition ore_check tm goal rank :=
  forallb (fun s => rank s <=? 4) ore_symbols &&
  forallb (fun q => forallb (ore_cell_ok tm goal rank q) ore_symbols) all_St.

Lemma ore_checked_rank : forall tm goal rank s,
  ore_check tm goal rank = true -> rank s <= 4.
Proof.
  intros tm goal rank s H. apply andb_prop in H as [H _].
  apply forallb_forall with (x:=s) in H; [apply Nat.leb_le; exact H|apply ore_symbols_complete].
Qed.
Lemma ore_checked_cell : forall tm goal rank q h,
  ore_check tm goal rank = true -> q <> goal ->
  exists tr, tm q h = Some tr /\
    (t_next tr = goal \/ (h <> S0 /\ (t_dir tr = DR -> rank (t_write tr) < rank h))).
Proof.
  intros tm goal rank q h H Hq.
  apply andb_prop in H as [_ H].
  apply forallb_forall with (x:=q) in H; [|apply all_St_complete].
  apply forallb_forall with (x:=h) in H; [|apply ore_symbols_complete].
  unfold ore_cell_ok in H. apply orb_true_iff in H as [H|H].
  { apply st_eqb_spec in H; contradiction. }
  destruct (tm q h) as [tr|] eqn:E; [|discriminate].
  exists tr. split; [reflexivity|].
  apply orb_true_iff in H as [H|H].
  - left. apply st_eqb_spec; exact H.
  - right. apply andb_prop in H as [Hh Hd]. split.
    + intro E0. subst h. discriminate.
    + intro Edr. rewrite Edr in Hd. apply Nat.ltb_lt; exact Hd.
Qed.
Lemma ore_reaches_step : forall tm goal cc cc',
  cstep tm cc = Some cc' -> ore_reaches tm goal cc' -> ore_reaches tm goal cc.
Proof.
  intros tm goal cc cc' Hs (k & cc'' & Hr & Hg).
  exists (S k), cc''. split; [cbn [csteps]; rewrite Hs; exact Hr|exact Hg].
Qed.
Lemma ore_blank_reaches : forall tm goal rank q l r,
  ore_check tm goal rank = true -> ore_reaches tm goal (q,(l,S0,r)).
Proof.
  intros tm goal rank q l r H.
  destruct (st_eqb q goal) eqn:E.
  - apply st_eqb_spec in E. exists 0, (q,(l,S0,r)); auto.
  - assert (Hq:q<>goal) by (intro Hq; subst; rewrite (proj2 (st_eqb_spec _ _) eq_refl) in E; discriminate).
    destruct (ore_checked_cell _ _ _ q S0 H Hq) as (tr & Htr & [Hg|[Hbad _]]); [|contradiction].
    exists 1, (t_next tr,ctape_move (t_dir tr) (t_write tr) (l,S0,r)).
    split; [rewrite csteps_1; unfold cstep; rewrite Htr; reflexivity|exact Hg].
Qed.

Theorem ore_check_reaches : forall tm goal rank,
  ore_check tm goal rank = true -> forall cc, ore_reaches tm goal cc.
Proof.
  intros tm goal rank Hcheck.
  apply (well_founded_induction_type (well_founded_ltof cconf (ore_measure rank))).
  intros [q [[l h] r]] IH.
  destruct (st_eqb q goal) eqn:E.
  { apply st_eqb_spec in E. exists 0, (q,(l,h,r)); auto. }
  assert (Hq:q<>goal) by (intro Hq; subst; rewrite (proj2 (st_eqb_spec _ _) eq_refl) in E; discriminate).
  destruct (ore_checked_cell _ _ _ q h Hcheck Hq) as (tr & Htr & Hnext).
  assert (Hstep:cstep tm (q,(l,h,r)) = Some (t_next tr,ctape_move (t_dir tr) (t_write tr) (l,h,r))).
  { unfold cstep. rewrite Htr. reflexivity. }
  destruct Hnext as [Hg|[Hh Hd]].
  { exists 1, (t_next tr,ctape_move (t_dir tr) (t_write tr) (l,h,r)).
    split; [rewrite csteps_1|]; assumption. }
  eapply ore_reaches_step; [exact Hstep|].
  destruct (t_dir tr) eqn:Edir; cbn [ctape_move].
  - destruct l as [|a l]; cbn [chd ctl].
    + eapply ore_blank_reaches; exact Hcheck.
    + apply IH. unfold ltof. change (ore_measure rank (q,(l,a,t_write tr::r)) < ore_measure rank (q,(a::l,h,r))).
      apply ore_left_drop. eapply ore_checked_rank; exact Hcheck.
  - destruct r as [|b r]; cbn [chd ctl].
    + eapply ore_blank_reaches; exact Hcheck.
    + apply IH. unfold ltof. change (ore_measure rank (q,(t_write tr::l,b,r)) < ore_measure rank (q,(l,h,b::r))).
      apply ore_right_drop. apply Hd; reflexivity.
Qed.

Definition ore_mirror_cc (cc : cconf) : cconf :=
  let '(q,(l,h,r)) := cc in (q,(r,h,l)).
Lemma ore_mirror_cstep : forall tm cc,
  cstep (mirror_tm tm) (ore_mirror_cc cc) = option_map ore_mirror_cc (cstep tm cc).
Proof.
  intros tm [q [[l h] r]]. unfold cstep, ore_mirror_cc, mirror_tm; cbn.
  destruct (tm q h) as [[w d q']|]; [destruct d|]; reflexivity.
Qed.
Lemma ore_mirror_csteps : forall tm k cc,
  csteps (mirror_tm tm) k (ore_mirror_cc cc) = option_map ore_mirror_cc (csteps tm k cc).
Proof.
  intros tm k; induction k; intro cc; [reflexivity|].
  cbn [csteps]. rewrite ore_mirror_cstep.
  destruct (cstep tm cc) as [cc'|]; cbn [option_map]; [apply IHk|reflexivity].
Qed.
Lemma ore_mirror_reaches : forall tm goal,
  (forall cc, ore_reaches (mirror_tm tm) goal cc) -> forall cc, ore_reaches tm goal cc.
Proof.
  intros tm goal H cc.
  destruct (H (ore_mirror_cc cc)) as (k & cc' & Hr & Hg).
  rewrite ore_mirror_csteps in Hr.
  destruct (csteps tm k cc) as [[q [[l h] r]]|] eqn:E; [|discriminate].
  injection Hr as <-. exists k, (q,(l,h,r)). auto.
Qed.

Record OReachCert := mkOReachCert {
  ore_mirrored : bool;
  ore_r0 : nat; ore_r1 : nat; ore_r2 : nat; ore_r3 : nat
}.
Definition ore_rank cert s := match s with
  S0=>ore_r0 cert | S1=>ore_r1 cert | S2=>ore_r2 cert | S3=>ore_r3 cert end.
Definition ore_cert_check tm goal cert :=
  ore_check (if ore_mirrored cert then mirror_tm tm else tm) goal (ore_rank cert).
Theorem ore_cert_reaches : forall tm goal cert,
  ore_cert_check tm goal cert = true -> forall cc, ore_reaches tm goal cc.
Proof.
  intros tm goal cert H. unfold ore_cert_check in H.
  destruct (ore_mirrored cert).
  - apply ore_mirror_reaches. eapply ore_check_reaches; exact H.
  - eapply ore_check_reaches; exact H.
Qed.

Lemma ore_reaches_total : forall tm,
  (forall goal cc, ore_reaches tm goal cc) -> Total tm.
Proof.
  intros tm H q s. destruct (tm q s) as [tr|] eqn:E; [eauto|].
  destruct (H (match q with StA=>StB|StB=>StA end) (q,([],s,[])))
    as (k & cc & Hr & Hg).
  destruct k.
  - injection Hr as <-. destruct q; discriminate.
  - cbn [csteps cstep] in Hr. rewrite E in Hr. discriminate.
Qed.
Lemma ore_total_csteps : forall tm, Total tm -> forall n cc,
  exists cc', csteps tm n cc = Some cc'.
Proof.
  intros tm Htotal n. induction n; intros [q [[l h] r]].
  - eexists; reflexivity.
  - destruct (Htotal q h) as (tr&Htr). cbn [csteps cstep]. rewrite Htr. apply IHn.
Qed.
Lemma ore_total_nonhalt : forall tm, Total tm -> NonHalt tm.
Proof.
  intros tm Htotal n Hnone.
  destruct (ore_total_csteps tm Htotal n c0) as (cc & Hc).
  pose proof (csteps_lift tm n c0 cc Hc) as Hrun.
  rewrite lift_c0,Hnone in Hrun. discriminate.
Qed.
Theorem ore_reaches_recurs : forall tm goal,
  Total tm -> (forall cc, ore_reaches tm goal cc) ->
  forall N, exists n, N <= n /\ VisitsAt tm goal n.
Proof.
  intros tm goal Htotal Hreach N.
  destruct (ore_total_csteps tm Htotal N c0) as (cc&Hprefix).
  destruct (Hreach cc) as (k&cc'&Htail&Hgoal).
  exists (N+k). split; [lia|]. exists (lift cc'). split; [|exact Hgoal].
  rewrite <- lift_c0. apply csteps_lift. rewrite csteps_add,Hprefix. exact Htail.
Qed.

Definition ore_state_check tm ca cb :=
  ore_cert_check tm StA ca && ore_cert_check tm StB cb.
Theorem ore_state_check_sound : forall tm ca cb,
  ore_state_check tm ca cb = true -> NonHalt tm /\ QHBound 0 tm.
Proof.
  intros tm ca cb H. apply andb_prop in H as [Ha Hb].
  assert (Hreach : forall goal cc, ore_reaches tm goal cc).
  { intros goal. destruct goal; eapply ore_cert_reaches; eauto. }
  assert (Htotal : Total tm) by (apply ore_reaches_total; exact Hreach).
  split; [apply ore_total_nonhalt; exact Htotal|].
  intros q s [_ Hquiet].
  destruct (ore_reaches_recurs tm q Htotal (Hreach q) (S s)) as (n&Hn&Hvisit).
  exfalso. apply (Hquiet n); [lia|exact Hvisit].
Qed.

Print Assumptions ore_check_reaches.
Print Assumptions ore_state_check_sound.

Definition ore_other q := match q with StA=>StB | StB=>StA end.
Fixpoint ore_rank_walk tm goal fuel s :=
  match fuel with
  | 0 => 0
  | S f => match tm (ore_other goal) s with
    | None => 0
    | Some tr => if st_eqb (t_next tr) goal then 0 else
      match t_dir tr with DL=>0 | DR=>S (ore_rank_walk tm goal f (t_write tr)) end
    end
  end.
Definition ore_auto_cert tm goal (mirrored : bool) :=
  let oriented := if mirrored then mirror_tm tm else tm in
  mkOReachCert mirrored
    (ore_rank_walk oriented goal 4 S0) (ore_rank_walk oriented goal 4 S1)
    (ore_rank_walk oriented goal 4 S2) (ore_rank_walk oriented goal 4 S3).
Definition ore_auto_goal tm goal :=
  ore_cert_check tm goal (ore_auto_cert tm goal false) ||
  ore_cert_check tm goal (ore_auto_cert tm goal true).
Definition ore_auto_state tm := ore_auto_goal tm StA && ore_auto_goal tm StB.
Lemma ore_auto_goal_sound : forall tm goal,
  ore_auto_goal tm goal = true -> forall cc, ore_reaches tm goal cc.
Proof.
  intros tm goal H. apply orb_true_iff in H as [H|H]; eapply ore_cert_reaches; exact H.
Qed.
Theorem ore_auto_state_sound : forall tm,
  ore_auto_state tm = true -> NonHalt tm /\ QHBound 0 tm.
Proof.
  intros tm H. apply andb_prop in H as [Ha Hb].
  assert (Hreach : forall goal cc, ore_reaches tm goal cc).
  { intros goal. destruct goal; apply ore_auto_goal_sound; assumption. }
  assert (Htotal : Total tm) by (apply ore_reaches_total; exact Hreach).
  split; [apply ore_total_nonhalt; exact Htotal|].
  intros q s [_ Hquiet].
  destruct (ore_reaches_recurs tm q Htotal (Hreach q) (S s)) as (n&Hn&Hvisit).
  exfalso. apply (Hquiet n); [lia|exact Hvisit].
Qed.
Print Assumptions ore_auto_state_sound.
