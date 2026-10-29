(** Transfer a proved B-start trajectory to an intersecting A-start trajectory.
    The two finite prefixes may have different lengths and need not leave a
    blank tape.  The target bound retains its entire prefix cost; no unproved
    equality of start states or reuse of a late anchor is assumed. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census
  Mirror CycleCensus Symmetry Shadow Closeout Pipeline FamilyTransport.
Import ListNotations.

Definition swap_cconf (c : cconf) : cconf := (swap_state (fst c), snd c).
Lemma lift_swap_cconf : forall c, lift (swap_cconf c)=swap_config (lift c).
Proof. reflexivity. Qed.
Definition meet_check tm destination source :=
  match csteps tm destination c0, csteps (swap_tm tm) source c0 with
  | Some a,Some b => ceqb a (swap_cconf b)
  | _,_ => false
  end.

Theorem meet_run : forall tm destination source,
  meet_check tm destination source=true -> forall k,
  stepn tm (destination+k) InitES=
  option_map swap_config (stepn (swap_tm tm) (source+k) InitES).
Proof.
  intros tm destination source H k. unfold meet_check in H.
  destruct (csteps tm destination c0) as [a|] eqn:Ea; [|discriminate].
  destruct (csteps (swap_tm tm) source c0) as [b|] eqn:Eb; [|discriminate].
  apply ceqb_lift in H. rewrite lift_swap_cconf in H.
  apply csteps_lift in Ea,Eb. rewrite lift_c0 in Ea,Eb.
  rewrite !stepn_add,Ea,Eb,H. apply swap_stepn.
Qed.

Section Meeting.
Variable tm : TM.
Variables destination source : nat.
Hypothesis meet : meet_check tm destination source=true.

Lemma meet_visits : forall q k,
  VisitsAt tm (swap_state q) (destination+k) <-> VisitsAt (swap_tm tm) q (source+k).
Proof.
  intros q k. unfold VisitsAt. rewrite (meet_run tm destination source meet).
  destruct (stepn (swap_tm tm) (source+k) InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); injection Hc as E; subst c'.
    + exists c; split; [reflexivity|].
      change (swap_state (fst c)=swap_state q) in Hq.
      apply (f_equal swap_state) in Hq. now rewrite !swap_state_involutive in Hq.
    + exists (swap_config c); split; [reflexivity|]. cbn [swap_config fst]. now rewrite Hq.
  - split; intros (c & Hc & _); discriminate.
Qed.
Lemma meet_fires : forall tg k,
  FiresAt tm (swap_instr tg) (destination+k) <-> FiresAt (swap_tm tm) tg (source+k).
Proof.
  intros tg k. unfold FiresAt. rewrite (meet_run tm destination source meet).
  destruct (stepn (swap_tm tm) (source+k) InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); injection Hc as E; subst c'.
    + exists c; split; [reflexivity|]. rewrite swap_config_instr in Hq.
      apply (f_equal swap_instr) in Hq. now rewrite !swap_instr_involutive in Hq.
    + exists (swap_config c); split; [reflexivity|]. now rewrite swap_config_instr,Hq.
  - split; intros (c & Hc & _); discriminate.
Qed.
Lemma meet_nonhalt : NonHalt (swap_tm tm) -> NonHalt tm.
Proof.
  intros Hnh n Hnone.
  assert (Htail : forall k, stepn tm (destination+k) InitES<>None).
  { intro k. rewrite (meet_run tm destination source meet).
    specialize (Hnh (source+k)). destruct (stepn (swap_tm tm) (source+k) InitES); cbn; congruence. }
  destruct (le_lt_dec destination n).
  - apply (Htail (n-destination)). now replace (destination+(n-destination)) with n by lia.
  - specialize (Htail 0). rewrite Nat.add_0_r in Htail.
    destruct (stepn tm destination InitES) as [c|] eqn:E; [|contradiction].
    destruct (stepn_prefix tm n destination InitES c ltac:(lia) E) as (c' & Hrun & _).
    congruence.
Qed.
Lemma meet_quiet : forall q n, destination<=n -> QuietAfter tm q n ->
  QuietAfter (swap_tm tm) (swap_state q) (source+(n-destination)).
Proof.
  intros q n Hn [Hv Hq]; split.
  - apply meet_visits. rewrite swap_state_involutive.
    now replace (destination+(n-destination)) with n by lia.
  - intros j Hj Hjv. apply (Hq (destination+(j-source))); [lia|].
    rewrite <- (swap_state_involutive q). apply meet_visits.
    now replace (source+(j-source)) with j by lia.
Qed.
Lemma meet_quiet_tr : forall tg n, destination<=n -> QuietAfterTr tm tg n ->
  QuietAfterTr (swap_tm tm) (swap_instr tg) (source+(n-destination)).
Proof.
  intros tg n Hn [Hv Hq]; split.
  - apply meet_fires. rewrite swap_instr_involutive.
    now replace (destination+(n-destination)) with n by lia.
  - intros j Hj Hjv. apply (Hq (destination+(j-source))); [lia|].
    rewrite <- (swap_instr_involutive tg). apply meet_fires.
    now replace (source+(j-source)) with j by lia.
Qed.
Theorem meet_bounds : forall bs bi,
  Bounds bs bi (swap_tm tm) ->
  Bounds (bs+N.of_nat destination)%N (bi+N.of_nat destination)%N tm.
Proof.
  intros bs bi [Hs Hi]; split; intros q n Hq; rewrite N2Nat.inj_add,Nat2N.id;
    destruct (le_lt_dec destination n).
  - pose proof (Hs _ _ (meet_quiet q n l Hq)); lia.
  - lia.
  - pose proof (Hi _ _ (meet_quiet_tr q n l Hq)); lia.
  - lia.
Qed.
End Meeting.

Definition conjugate_check tm core p mirrored destination source :=
  table_leb core (shadow_transform p mirrored tm) && meet_check tm destination source.
Theorem conjugate_check_sound : forall tm core p mirrored destination source bs bi,
  conjugate_check tm core p mirrored destination source=true ->
  NonHalt core -> Bounds bs bi core ->
  NonHalt tm /\ Bounds (bs+N.of_nat destination)%N (bi+N.of_nat destination)%N tm.
Proof.
  intros tm core p mirrored destination source bs bi H Hnh Hb.
  apply andb_prop in H as [Htable Hmeet]. apply table_leb_spec in Htable.
  pose proof (completion_strong bs bi core _ (conj Hnh Hb) Htable) as [Hn Hb'].
  unfold shadow_transform in Hn,Hb'. destruct mirrored.
  - apply mirror_nonhalt in Hn. apply mirror_bounds in Hb'.
    apply perm_nonhalt in Hn. apply perm_bounds in Hb'.
    split; [eapply meet_nonhalt|eapply meet_bounds]; eauto.
  - apply perm_nonhalt in Hn. apply perm_bounds in Hb'.
    split; [eapply meet_nonhalt|eapply meet_bounds]; eauto.
Qed.

Record ConjugateRow := conjugate_row {
  conjugate_codes : list nat;
  conjugate_source : nat;
  conjugate_permutation : SymPerm;
  conjugate_mirrored : bool;
  destination_boot : nat;
  source_boot : nat
}.
Definition conjugate_tm row := machine_of_codes (conjugate_codes row).
Definition conjugate_row_check bs bi out_bs out_bi board row :=
  (conjugate_source row <? length board) &&
  ((bs+N.of_nat (destination_boot row) <=? out_bs)%N) &&
  ((bi+N.of_nat (destination_boot row) <=? out_bi)%N) &&
  conjugate_check (conjugate_tm row) (nth (conjugate_source row) board empty)
    (conjugate_permutation row) (conjugate_mirrored row) (destination_boot row) (source_boot row).
Theorem conjugate_row_sound : forall bs bi out_bs out_bi board row,
  StrongBoard bs bi board -> conjugate_row_check bs bi out_bs out_bi board row=true ->
  NonHalt (conjugate_tm row) /\ Bounds out_bs out_bi (conjugate_tm row).
Proof.
  intros bs bi out_bs out_bi board row Hboard H.
  apply andb_prop in H as [H Hcheck]. apply andb_prop in H as [H Hbi].
  apply andb_prop in H as [Hindex Hbs].
  apply Nat.ltb_lt in Hindex. apply N.leb_le in Hbs,Hbi.
  destruct (Hboard _ (nth_In _ empty Hindex)) as [Hnh Hb].
  destruct (conjugate_check_sound _ _ _ _ _ _ _ _ Hcheck Hnh Hb) as [Hnh' Hb'].
  split; [exact Hnh'|]. eapply bounds_weaken; eauto.
Qed.
Theorem conjugate_batch_sound : forall bs bi out_bs out_bi board rows,
  StrongBoard bs bi board -> forallb (conjugate_row_check bs bi out_bs out_bi board) rows=true ->
  StrongBoard out_bs out_bi (map conjugate_tm rows).
Proof.
  intros bs bi out_bs out_bi board rows Hboard H tm Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply conjugate_row_sound; eauto.
Qed.

Print Assumptions conjugate_check_sound.
Print Assumptions conjugate_batch_sound.
