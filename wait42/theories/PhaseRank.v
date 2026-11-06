(** Scratch reflected composition of monotone control phases. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport ControlRank.
Import ListNotations.
Record phase_rank := mkPhaseRank {
 ph_label : St -> nat; ph_cycles : nat -> nat;
 ph_cyclic : nat -> bool; ph_dir : nat -> Dir }.
Definition phase_level (p : phase_rank) s := ph_label p s.
Definition phase_cycles (p : phase_rank) s := ph_cycles p (ph_label p s).
Definition phase_cyclic (p : phase_rank) s := ph_cyclic p (ph_label p s).
Definition phase_horizon (c r t : nat) :=
 match c with 0 => t+r+6 | 1 => 2*(t+r+6) | _ => 4*(t+r+6) end.
Lemma phase_horizon_ge : forall c r t, t <= phase_horizon c r t.
Proof. intros [|[|c]] r t; cbn [phase_horizon]; lia. Qed.
Lemma phase_horizon_acyclic : forall c c' r r' t t',
 c <= 2 -> c' <= c -> r' < r -> t' <= t+1 ->
 phase_horizon c' r' t' <= phase_horizon c r t.
Proof.
 intros c c' r r' t t' Hc Hc' Hr Ht.
 destruct c as [|[|[|c]]], c' as [|[|[|c']]]; cbn [phase_horizon]; nia.
Qed.
Lemma phase_horizon_cyclic : forall c c' r r' t t',
 c <= 2 -> c' < c -> r' < r -> t' <= 2*t+6 ->
 phase_horizon c' r' t' <= phase_horizon c r t.
Proof.
 intros c c' r r' t t' Hc Hc' Hr Ht.
 destruct c as [|[|[|c]]], c' as [|[|[|c']]]; cbn [phase_horizon]; nia.
Qed.
Lemma phase_horizon_cost : forall c r t j cyclic,
 c <= 2 -> (cyclic = true -> 0 < c) ->
 j <= (if cyclic then t+6 else 1) -> t+j <= phase_horizon c r t.
Proof.
 intros c r t j cyclic Hc Hp Hj.
 destruct cyclic; specialize (Hp eq_refl) || idtac;
 destruct c as [|[|[|c]]]; cbn [phase_horizon] in *; nia.
Qed.
Lemma phase_horizon_initial : forall c r B,
 c <= 2 -> r <= 4 -> phase_horizon c r B <= 4*B+40.
Proof. intros [|[|[|c]]] r B Hc Hr; cbn [phase_horizon]; nia. Qed.

Definition phase_progress (p : phase_rank) (s s' : St) :=
 phase_level p s' < phase_level p s /\
 phase_cycles p s' <= phase_cycles p s /\
 (phase_cyclic p s = true -> phase_cycles p s' < phase_cycles p s).
Definition phase_wf (p : phase_rank) (s : St) :=
 phase_level p s <= 4 /\ phase_cycles p s <= 2 /\
 (phase_cyclic p s = true -> 0 < phase_cycles p s).
Definition phase_future tm q c :=
 exists n cq, stepn tm n c = Some cq /\ fst cq = q.

(** This interface is discharged by the reflected monotone-phase checker:
    the selected exit preserves a future target witness, as well as giving
    strict control-phase progress. No arbitrary late exit can be substituted. *)
Definition phase_macro_sound tm (inv : St -> bool) q p :=
 forall t c, stepn tm t InitES = Some c -> inv (fst c) = true -> fst c <> q ->
 phase_future tm q c -> exists j c',
 stepn tm j c = Some c' /\ inv (fst c') = true /\ phase_future tm q c' /\
 j <= (if phase_cyclic p (fst c) then t+6 else 1) /\
 (fst c' = q \/ phase_progress p (fst c) (fst c')).

Lemma phase_composition_reach : forall tm inv q p,
 phase_macro_sound tm inv q p ->
 (forall s, inv s = true -> s <> q -> phase_wf p s) ->
 forall r t c, phase_level p (fst c) < r ->
 stepn tm t InitES = Some c -> inv (fst c) = true -> phase_future tm q c ->
 exists j cq, t+j <= phase_horizon (phase_cycles p (fst c)) (phase_level p (fst c)) t /\
 stepn tm j c = Some cq /\ fst cq = q.
Proof.
 intros tm inv q p HM HW r. induction r as [|r IH]; intros t c Hr Hrun HI HF; [lia|].
 destruct (st_eqb (fst c) q) eqn:Eq.
 - apply st_eqb_spec in Eq. exists 0,c. split; [rewrite Nat.add_0_r; apply phase_horizon_ge|]. auto.
 - assert (Hneq : fst c <> q).
   { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
   destruct (HW (fst c) HI Hneq) as [Hlevel [Hcycles Hpos]].
   destruct (HM t c Hrun HI Hneq HF) as (j & c' & Hstep & HI' & HF' & Hj & HP).
   destruct HP as [Htarget|HP].
   + exists j,c'. split; [|auto].
     eapply phase_horizon_cost; eauto.
   + destruct HP as [Hlevel' [Hcycles' Hstrict]].
     assert (Hrun' : stepn tm (t+j) InitES = Some c').
     { rewrite stepn_add,Hrun; exact Hstep. }
     destruct (IH (t+j) c' ltac:(lia) Hrun' HI' HF')
       as (k & cq & Hbound & Hsteps & Hq).
     assert (Hhor : phase_horizon (phase_cycles p (fst c')) (phase_level p (fst c')) (t+j)
       <= phase_horizon (phase_cycles p (fst c)) (phase_level p (fst c)) t).
     { destruct (phase_cyclic p (fst c)) eqn:HC.
       - eapply phase_horizon_cyclic; eauto; specialize (Hstrict eq_refl); lia.
       - eapply phase_horizon_acyclic; eauto; lia. }
     exists (j+k),cq. split; [lia|]. split; [|exact Hq].
     rewrite stepn_add,Hstep. exact Hsteps.
Qed.

Theorem phase_composition_window : forall tm inv q p B cB,
 phase_macro_sound tm inv q p ->
 (forall s, inv s = true -> s <> q -> phase_wf p s) ->
 stepn tm B InitES = Some cB -> inv (fst cB) = true -> FutureBeep tm q B ->
 BeepWindow tm q B (3*B+100).
Proof.
 intros tm inv q p B cB HM HW HB HI (u & Hu & cq & Hrun & Hq).
 assert (HF : phase_future tm q cB).
 { exists (u-B),cq. split; [|exact Hq].
   replace u with (B+(u-B)) in Hrun by lia; rewrite stepn_add,HB in Hrun; exact Hrun. }
 destruct (st_eqb (fst cB) q) eqn:Eq.
 - apply st_eqb_spec in Eq. exists B. repeat split; try lia. exists cB; auto.
 - assert (Hneq : fst cB <> q).
   { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
   destruct (HW (fst cB) HI Hneq) as [Hlevel [Hcycles Hpos]].
   destruct (phase_composition_reach tm inv q p HM HW (S (phase_level p (fst cB)))
     B cB ltac:(lia) HB HI HF) as (j & d & Hj & Hd & Htarget).
   pose proof (phase_horizon_initial _ _ B Hcycles Hlevel).
   exists (B+j). repeat split; try lia.
   exists d. split; [rewrite stepn_add,HB; exact Hd|exact Htarget].
Qed.

From BBBWait42 Require Import MonotonePhase.
Definition phase_set inv q p label s :=
 inv s && negb (st_eqb s q) && Nat.eqb (ph_label p s) label.
Lemma phase_set_spec : forall inv q p label s,
 phase_set inv q p label s = true <->
 inv s = true /\ s <> q /\ ph_label p s = label.
Proof.
 intros inv q p label s. unfold phase_set.
 rewrite andb_true_iff,andb_true_iff,negb_true_iff,Nat.eqb_eq.
 split.
 - intros [[HI Hn] HL]. split; [exact HI|]. split; [|exact HL].
   intro E; subst s. assert (st_eqb q q=true) by (apply st_eqb_spec; reflexivity). congruence.
 - intros [HI [Hn HL]]. repeat split; auto.
   destruct (st_eqb s q) eqn:E; auto. apply st_eqb_spec in E; contradiction.
Qed.
Lemma phase_set_target_false : forall inv q p label,
 phase_set inv q p label q = false.
Proof. intros inv q p label. unfold phase_set. destruct q; simpl; rewrite andb_false_r; reflexivity. Qed.
Definition phase_wf_ok p s :=
 (phase_level p s <=? 4) && (phase_cycles p s <=? 2) &&
 (if phase_cyclic p s then 0 <? phase_cycles p s else true).
Definition phase_edge_ok p q s tr :=
 if st_eqb s q || st_eqb (t_next tr) q then true else
 if Nat.eqb (ph_label p (t_next tr)) (ph_label p s) then
 phase_cyclic p s && phase_dir_eqb (t_dir tr) (ph_dir p (ph_label p s)) else
 (phase_level p (t_next tr) <? phase_level p s) &&
 (phase_cycles p (t_next tr) <=? phase_cycles p s) &&
 (if phase_cyclic p s then phase_cycles p (t_next tr) <? phase_cycles p s else true).
Definition phase_target_ok tm inv q p :=
 forallb (fun s => if inv s && negb (st_eqb s q) then
 phase_wf_ok p s &&
 forallb (fun h => match tm s h with Some tr => phase_edge_ok p q s tr |None=>false end) cr_symbols &&
 (if phase_cyclic p s then phase_check tm (phase_set inv q p (ph_label p s))
   (ph_dir p (ph_label p s)) else true)
 else true) all_St.
Definition phase_checks_ok (tm : TM) (inv : St -> bool) (cert : St -> phase_rank) :=
 forallb (fun q => if inv q then phase_target_ok tm inv q (cert q) else true) all_St.
Definition control_phase_check (tm : TM) (inv : St -> bool)
 (cert : St -> phase_rank) (anchor : nat) (B w : N) :=
 N.leb (N.of_nat anchor) B && N.leb (3*B+100)%N w &&
 match csteps tm anchor c0 with
 | Some seed => inv (fst seed) && cr_closed_ok tm inv && phase_checks_ok tm inv cert
 | None => false end.

Lemma phase_target_entry : forall tm inv q p,
 phase_target_ok tm inv q p = true -> forall s,
 inv s = true -> s <> q ->
 phase_wf_ok p s = true /\
 (forall h tr, tm s h = Some tr -> phase_edge_ok p q s tr = true) /\
 (phase_cyclic p s = true -> phase_check tm (phase_set inv q p (ph_label p s))
   (ph_dir p (ph_label p s)) = true).
Proof.
 intros tm inv q p H s HI Hn. unfold phase_target_ok in H.
 rewrite forallb_forall in H; specialize (H s (all_St_complete s)).
 assert (Es : st_eqb s q = false).
 { destruct (st_eqb s q) eqn:E; auto. apply st_eqb_spec in E; contradiction. }
 rewrite HI,Es in H; cbv beta iota zeta delta [andb negb] in H.
 apply andb_true_iff in H as [H Hsweep]. apply andb_true_iff in H as [Hw He].
 split; [exact Hw|]. split.
 - intros h tr Et. rewrite forallb_forall in He.
   specialize (He h (cr_symbols_complete h)); rewrite Et in He; exact He.
 - intro HC; rewrite HC in Hsweep; exact Hsweep.
Qed.
Lemma phase_wf_ok_sound : forall p s, phase_wf_ok p s = true -> phase_wf p s.
Proof.
 intros p s H. unfold phase_wf_ok in H; unfold phase_wf.
 apply andb_true_iff in H as [H Hp]. apply andb_true_iff in H as [Hl Hc].
 apply Nat.leb_le in Hl; apply Nat.leb_le in Hc. repeat split; auto.
 intro HC; rewrite HC in Hp; apply Nat.ltb_lt; exact Hp.
Qed.
Lemma phase_edge_analysis : forall p q s tr,
 phase_edge_ok p q s tr = true -> s <> q -> t_next tr <> q ->
 (ph_label p (t_next tr) = ph_label p s /\ phase_cyclic p s = true) \/
 phase_progress p s (t_next tr).
Proof.
 intros p q s tr H Hs Hs'. unfold phase_edge_ok in H.
 assert (Es : st_eqb s q = false).
 { destruct (st_eqb s q) eqn:E; auto; apply st_eqb_spec in E; contradiction. }
 assert (Es' : st_eqb (t_next tr) q = false).
 { destruct (st_eqb (t_next tr) q) eqn:E; auto; apply st_eqb_spec in E; contradiction. }
 rewrite Es,Es' in H; cbn in H.
 destruct (Nat.eqb (ph_label p (t_next tr)) (ph_label p s)) eqn:EL.
 - apply Nat.eqb_eq in EL. apply andb_true_iff in H as [HC _]. left; auto.
 - apply andb_true_iff in H as [H Hp]. apply andb_true_iff in H as [Hl Hc].
   apply Nat.ltb_lt in Hl; apply Nat.leb_le in Hc. right. repeat split; auto.
   intro HC; rewrite HC in Hp; apply Nat.ltb_lt; exact Hp.
Qed.
Lemma phase_exec_inv_step : forall tm inv,
 cr_closed_ok tm inv = true -> forall c c', inv (fst c) = true ->
 step tm c = Some c' -> inv (fst c') = true.
Proof.
 intros tm inv H [s tp] c' HI Hstep.
 destruct (cr_closed_step tm inv H s (t_head tp) HI) as (tr & Et & HI').
 unfold step in Hstep; rewrite Et in Hstep; injection Hstep as <-; exact HI'.
Qed.
Lemma phase_exec_inv_run : forall tm inv,
 cr_closed_ok tm inv = true -> forall n c c', inv (fst c) = true ->
 stepn tm n c = Some c' -> inv (fst c') = true.
Proof.
 intros tm inv HC n. induction n as [|n IH]; intros c c' HI HR.
 - cbn [stepn] in HR; injection HR as <-; exact HI.
 - cbn [stepn] in HR; destruct (step tm c) as [d|] eqn:HS; [|discriminate].
   eapply IH; [eapply phase_exec_inv_step; eauto|exact HR].
Qed.
Lemma phase_actual_edge : forall tm inv q p,
 phase_target_ok tm inv q p = true -> forall c c',
 inv (fst c) = true -> fst c <> q -> fst c' <> q -> step tm c = Some c' ->
 (ph_label p (fst c') = ph_label p (fst c) /\ phase_cyclic p (fst c) = true) \/
 phase_progress p (fst c) (fst c').
Proof.
 intros tm inv q p H [s tp] c' HI Hs Hs' HS.
 destruct (phase_target_entry tm inv q p H s HI Hs) as [_ [HE _]].
 unfold step in HS; destruct (tm s (t_head tp)) as [tr|] eqn:Et; [|discriminate].
 injection HS as <-. apply (phase_edge_analysis p q s tr (HE _ _ Et) Hs Hs').
Qed.

Lemma phase_checked_macro : forall tm inv q p,
 cr_closed_ok tm inv = true -> phase_target_ok tm inv q p = true ->
 phase_macro_sound tm inv q p.
Proof.
 intros tm inv q p HC HT t c Hrun HI Hn (N & target & HR & Hq).
 destruct (phase_target_entry tm inv q p HT (fst c) HI Hn) as [HW [HE HP]].
 destruct (phase_cyclic p (fst c)) eqn:HCyc.
 - assert (Hphase : phase_set inv q p (ph_label p (fst c)) (fst c) = true).
   { apply phase_set_spec; auto. }
   destruct (phase_check_exit_before tm (phase_set inv q p (ph_label p (fst c)))
     (ph_dir p (ph_label p (fst c))) t c N target (HP eq_refl) Hrun Hphase HR
     ltac:(rewrite Hq; apply phase_set_target_false))
     as (j & d & Hj & HjN & HX & Htail).
   destruct (phase_exit_run _ _ _ _ _ HX) as [Hjpos [Hsteps [_ Hout]]].
   assert (HId : inv (fst d) = true) by (eapply phase_exec_inv_run; eauto).
   exists j,d. split; [exact Hsteps|]. split; [exact HId|]. split.
   + exists (N-j),target; auto.
   + split; [lia|]. destruct (st_eqb (fst d) q) eqn:Eq.
     * apply st_eqb_spec in Eq. left; exact Eq.
     * assert (Hnd : fst d <> q).
       { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
       destruct (phase_exit_last _ _ _ _ _ HX) as (last & Hlast & Hinside & Hstep).
       apply phase_set_spec in Hinside as [HIl [Hnl Hlabel]].
       destruct (phase_actual_edge tm inv q p HT last d HIl Hnl Hnd Hstep) as [[Heq _]|Hprog].
       -- assert (Hyes : phase_set inv q p (ph_label p (fst c)) (fst d) = true).
          { apply phase_set_spec; repeat split; auto; congruence. }
          congruence.
       -- right. unfold phase_progress,phase_level,phase_cycles,phase_cyclic in *.
          rewrite Hlabel in Hprog. exact Hprog.
 - destruct N as [|N].
   { cbn [stepn] in HR; injection HR as <-; contradiction. }
   cbn [stepn] in HR; destruct (step tm c) as [d|] eqn:HS; [|discriminate].
   exists 1,d. split; [cbn [stepn]; rewrite HS; reflexivity|].
   split; [eapply phase_exec_inv_step; eauto|]. split; [exists N,target; auto|].
   split; [lia|]. destruct (st_eqb (fst d) q) eqn:Eq.
   + apply st_eqb_spec in Eq. left; exact Eq.
   + assert (Hnd : fst d <> q).
     { intro E; apply st_eqb_spec in E; rewrite E in Eq; discriminate. }
     destruct (phase_actual_edge tm inv q p HT c d HI Hn Hnd HS) as [[_ Hbad]|Hgood].
     * congruence.
     * right; exact Hgood.
Qed.

Theorem control_phase_check_sound : forall tm inv cert anchor B w,
 control_phase_check tm inv cert anchor B w = true ->
 NonHalt tm /\ WindowBound tm (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv cert anchor B w H. unfold control_phase_check in H.
 apply andb_true_iff in H as [Hg H].
 apply andb_true_iff in Hg as [Ha Hw].
 apply N.leb_le in Ha; apply cr_N_le_nat in Ha; rewrite Nat2N.id in Ha.
 apply N.leb_le in Hw; apply cr_N_le_nat in Hw.
 rewrite N2Nat.inj_add,N2Nat.inj_mul in Hw.
 change (3*N.to_nat B+100 <= N.to_nat w) in Hw.
 destruct (csteps tm anchor c0) as [seed|] eqn:HA; [|discriminate].
 apply andb_true_iff in H as [H HT]; apply andb_true_iff in H as [HI HC].
 assert (Hanchor : stepn tm anchor InitES = Some (lift seed)).
 { rewrite <- lift_c0; apply csteps_lift; exact HA. }
 assert (Hinv : forall t c, anchor <= t -> stepn tm t InitES = Some c -> inv (fst c) = true).
 { intros t c Hat HR. replace t with (anchor+(t-anchor)) in HR by lia.
   rewrite stepn_add,Hanchor in HR.
   exact (phase_exec_inv_run tm inv HC (t-anchor) (lift seed) c HI HR). }
 split.
 - intros n Hnone.
   assert (Hrun : forall k c, inv (fst c) = true -> exists d, csteps tm k c = Some d).
   { induction k as [|k IH]; intros [s [[l h] r]] HIs.
     - eexists; reflexivity.
     - destruct (cr_closed_step tm inv HC s h HIs) as (tr & Et & HIt).
       destruct (IH (t_next tr,ctape_move (t_dir tr) (t_write tr) (l,h,r)) HIt) as [d Hd].
       exists d; cbn [csteps cstep]; rewrite Et; exact Hd. }
   destruct (Hrun n seed HI) as [d Hd].
   assert (Hlong : stepn tm (anchor+n) InitES = Some (lift d)).
   { rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add,HA; exact Hd. }
   replace (anchor+n) with (n+anchor) in Hlong by lia.
   rewrite stepn_add,Hnone in Hlong; discriminate.
 - intros q HF. destruct HF as (u & Hu & cq & HR & Hq).
   assert (HIq : inv q = true).
   { rewrite <- Hq. exact (Hinv u cq ltac:(lia) HR). }
   unfold phase_checks_ok in HT; rewrite forallb_forall in HT.
   specialize (HT q (all_St_complete q)); rewrite HIq in HT.
   assert (HWf : forall s, inv s = true -> s <> q -> phase_wf (cert q) s).
   { intros s HIs Hneq; apply phase_wf_ok_sound.
     exact (proj1 (phase_target_entry tm inv q (cert q) HT s HIs Hneq)). }
   destruct (stepn_prefix tm (N.to_nat B) u InitES cq Hu HR) as (cB & HB & Htail).
   assert (HIB : inv (fst cB) = true) by (exact (Hinv (N.to_nat B) cB Ha HB)).
   assert (HF : FutureBeep tm q (N.to_nat B)) by (exists u; split; [exact Hu|exists cq; auto]).
   destruct (phase_composition_window tm inv q (cert q) (N.to_nat B) cB
     (phase_checked_macro tm inv q (cert q) HC HT) HWf HB HIB HF)
     as (v & Hv & Hvb & Hvq).
   exists v; repeat split; auto; lia.
Qed.
Theorem control_phase_check_completion : forall tm inv cert anchor B w,
 control_phase_check tm inv cert anchor B w = true ->
 forall tm', TM_le tm tm' -> NonHalt tm' /\ WindowBound tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv cert anchor B w H tm' Hle.
 destruct (control_phase_check_sound tm inv cert anchor B w H) as [HN HW].
 split; [eapply nonhalt_le; eauto|].
 apply (proj2 (window_bound_completion tm tm' (N.to_nat B) (N.to_nat w) HN Hle)); exact HW.
Qed.
Record phase_case := mkPhaseCase {
 phase_machine : TM; phase_inv : St -> bool;
 phase_cert : St -> phase_rank; phase_anchor : nat }.
Definition control_phase_batch_check (entries : list phase_case) (B w : N) :=
 forallb (fun e => control_phase_check (phase_machine e) (phase_inv e)
  (phase_cert e) (phase_anchor e) B w) entries.
Theorem control_phase_batch_completion : forall entries B w,
 control_phase_batch_check entries B w = true ->
 forall e, In e entries -> forall tm', TM_le (phase_machine e) tm' ->
 NonHalt tm' /\ WindowBound tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros entries B w H e Hin tm' Hle. unfold control_phase_batch_check in H.
 rewrite forallb_forall in H.
 exact (control_phase_check_completion (phase_machine e) (phase_inv e)
  (phase_cert e) (phase_anchor e) B w (H e Hin) tm' Hle).
Qed.
Print Assumptions phase_composition_window.
Print Assumptions control_phase_check_completion.
Print Assumptions control_phase_batch_completion.
