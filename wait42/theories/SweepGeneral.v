(** Conditional blank sweeps, allowing either self-scan symbol. *)
From Coq Require Import Arith Lia Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport Sweep.

Definition other_sym (s : Sym) := match s with S0 => S1 | S1 => S0 end.

(** A finite target witness exhibits a one in the original untouched half
    tape. Writes behind a monotone scan do not change that witness. *)
Lemma zero_scan_future_exit : forall tm p q d w0 w1 d1,
 p <> q ->
 tm p S0 = Some (mkTrans w0 d p) ->
 tm p S1 = Some (mkTrans w1 d1 q) ->
 forall t tp cq, stepn tm t (p,tp) = Some cq -> fst cq = q ->
 exists n j cq', ahead d tp n = S1 /\ j <= S n /\
   stepn tm j (p,tp) = Some cq' /\ fst cq' = q.
Proof.
 intros tm p q d w0 w1 d1 Hneq H0 H1 t.
 induction t as [|t IH]; intros tp cq Hrun Hq.
 - cbn [stepn] in Hrun; injection Hrun as <-; contradiction.
 - destruct (t_head tp) eqn:Eh.
   + cbn [stepn step] in Hrun; rewrite Eh,H0 in Hrun.
     destruct (IH _ cq Hrun Hq) as (n & j & cq' & Ha & Hj & Hr & Hcq).
     exists (S n),(S j),cq'. split.
     * rewrite <- (ahead_move d tp w0 n); exact Ha.
     * split; [lia|]; split; [|exact Hcq].
       cbn [stepn step]; rewrite Eh,H0; exact Hr.
   + exists 0,1,(q,tape_move d1 w1 tp). split; [exact Eh|].
     split; [lia|]; split; [|reflexivity].
     cbn [stepn step]; rewrite Eh,H1; reflexivity.
Qed.

Lemma zero_scan_from_cutoff : forall tm p q d w0 w1 d1 B tp,
 p <> q ->
 tm p S0 = Some (mkTrans w0 d p) ->
 tm p S1 = Some (mkTrans w1 d1 q) ->
 stepn tm B InitES = Some (p,tp) -> FutureBeep tm q B ->
 BeepWindow tm q B (B+2).
Proof.
 intros tm p q d w0 w1 d1 B tp Hneq H0 H1 HB
   (t & Ht & cq & Hrun & Hq).
 replace t with (B+(t-B)) in Hrun by lia; rewrite stepn_add,HB in Hrun.
 destruct (zero_scan_future_exit tm p q d w0 w1 d1 Hneq H0 H1
   (t-B) tp cq Hrun Hq) as (n & j & cq' & Ha & Hj & Hr & Hcq).
 assert (Hn : n <= B).
 { destruct n as [|n]; [lia|].
   destruct (le_dec B n) as [Hle|Hle]; [|lia].
   pose proof (blank_radius_from_blank tm B (p,tp) HB n Hle) as [Hl Hright].
   change (t_left tp n = S0) in Hl; change (t_right tp n = S0) in Hright.
   destruct d; cbn [ahead] in Ha; congruence. }
 exists (B+j); repeat split; try lia.
 exists cq'; split; [rewrite stepn_add,HB; exact Hr|exact Hcq].
Qed.

Lemma symbol_scan_from_cutoff : forall tm p q s d ws wx dx B tp,
 p <> q ->
 tm p s = Some (mkTrans ws d p) ->
 tm p (other_sym s) = Some (mkTrans wx dx q) ->
 stepn tm B InitES = Some (p,tp) -> FutureBeep tm q B ->
 BeepWindow tm q B (B+2).
Proof.
 intros tm p q s d ws wx dx B tp Hneq Hs Hx HB HF.
 destruct s.
 - exact (zero_scan_from_cutoff tm p q d ws wx dx B tp Hneq Hs Hx HB HF).
 - exact (sweep_from_cutoff tm p q d ws wx dx B tp Hs Hx HB).
Qed.

Section GeneralPair.
Variable tm : TM.
Variable p q : St.
Variable sp sq : Sym.
Variable dp dq ep eq : Dir.
Variable wp wq zp zq : Sym.
Hypothesis Hneq : p <> q.
Hypothesis Hps : tm p sp = Some (mkTrans wp dp p).
Hypothesis Hpx : tm p (other_sym sp) = Some (mkTrans zp ep q).
Hypothesis Hqs : tm q sq = Some (mkTrans wq dq q).
Hypothesis Hqx : tm q (other_sym sq) = Some (mkTrans zq eq p).

Lemma general_pair_step : forall c, fst c = p \/ fst c = q ->
 exists c', step tm c = Some c' /\ (fst c' = p \/ fst c' = q).
Proof.
 intros [r tp] [Hr|Hr]; cbn in Hr; subst r.
 - destruct sp; cbn [other_sym] in Hpx; destruct (t_head tp) eqn:Eh; cbn [step]; rewrite Eh;
     first [rewrite Hps | rewrite Hpx]; eexists; split; try reflexivity; cbn; auto.
 - destruct sq; cbn [other_sym] in Hqx; destruct (t_head tp) eqn:Eh; cbn [step]; rewrite Eh;
     first [rewrite Hqs | rewrite Hqx]; eexists; split; try reflexivity; cbn; auto.
Qed.
Lemma general_pair_run : forall n c, fst c = p \/ fst c = q ->
 exists c', stepn tm n c = Some c' /\ (fst c' = p \/ fst c' = q).
Proof.
 induction n as [|n IH]; intros c HC.
 - exists c; split; auto.
 - destruct (general_pair_step c HC) as (c1 & HS & HC1).
   destruct (IH c1 HC1) as (c' & Hr & HC').
   exists c'; split; [cbn [stepn]; rewrite HS; exact Hr|exact HC'].
Qed.
Variable anchor : nat.
Variable ca : ExecState.
Hypothesis HA : stepn tm anchor InitES = Some ca.
Hypothesis HC : fst ca = p \/ fst ca = q.
Lemma general_pair_at : forall B, anchor <= B ->
 exists c, stepn tm B InitES = Some c /\ (fst c = p \/ fst c = q).
Proof.
 intros B HB; destruct (general_pair_run (B-anchor) ca HC) as (c & Hr & Hc).
 exists c; split; [|exact Hc].
 replace B with (anchor+(B-anchor)) by lia; rewrite stepn_add,HA; exact Hr.
Qed.
Theorem general_pair_nonhalt : NonHalt tm.
Proof.
 intros n Hnone; destruct (le_dec anchor n) as [Hle|Hle].
 - destruct (general_pair_at n Hle) as (c & Hr & _); congruence.
 - destruct (stepn_prefix tm n anchor InitES ca ltac:(lia) HA) as (c & Hr & _); congruence.
Qed.
Theorem general_pair_window : forall B, anchor <= B -> WindowBound tm B (B+2).
Proof.
 intros B HB r HF; destruct HF as (t & Ht & ct & Hrun & Hr).
 destruct (general_pair_at t ltac:(lia)) as (ct' & Hrun' & Hct).
 rewrite Hrun in Hrun'; injection Hrun' as <-.
 destruct (general_pair_at B HB) as ([s tp] & HBRun & Hs).
 cbn in Hs; destruct Hct as [Hp|Hq];
   [assert (Er : r=p) by congruence|assert (Er : r=q) by congruence]; rewrite Er.
 - destruct Hs as [Hs|Hs]; subst s.
   + exists B; repeat split; try lia; exists (p,tp); auto.
   + eapply (symbol_scan_from_cutoff tm q p sq dq wq zq eq B tp).
     * congruence.
     * exact Hqs.
     * exact Hqx.
     * exact HBRun.
     * exists t; split; [exact Ht|exists ct; split; [exact Hrun|congruence]].
 - destruct Hs as [Hs|Hs]; subst s.
   + eapply (symbol_scan_from_cutoff tm p q sp dp wp zp ep B tp).
     * exact Hneq.
     * exact Hps.
     * exact Hpx.
     * exact HBRun.
     * exists t; split; [exact Ht|exists ct; split; [exact Hrun|congruence]].
   + exists B; repeat split; try lia; exists (q,tp); auto.
Qed.
End GeneralPair.

Definition general_sweep_check (tm : TM) (anchor : nat) (p q : St) (sp sq : Sym) :=
 negb (st_eqb p q) &&
 match tm p sp, tm p (other_sym sp), tm q sq, tm q (other_sym sq), csteps tm anchor c0 with
 | Some ps, Some px, Some qs, Some qx, Some ca =>
   st_eqb (t_next ps) p && st_eqb (t_next px) q &&
   st_eqb (t_next qs) q && st_eqb (t_next qx) p &&
   (st_eqb (fst ca) p || st_eqb (fst ca) q)
 | _,_,_,_,_ => false end.

Theorem general_sweep_check_sound : forall tm anchor p q sp sq,
 general_sweep_check tm anchor p q sp sq = true ->
 NonHalt tm /\ forall B, anchor <= B -> WindowBound tm B (B+2).
Proof.
 intros tm anchor p q sp sq H; unfold general_sweep_check in H.
 apply andb_true_iff in H as [Hneq H].
 apply negb_true_iff in Hneq.
 assert (Hpq : p <> q).
 { intro E; subst q; rewrite st_eqb_refl in Hneq; discriminate. }
 destruct (tm p sp) as [[wp dp ps]|] eqn:Hps; [|discriminate].
 destruct (tm p (other_sym sp)) as [[zp ep px]|] eqn:Hpx; [|discriminate].
 destruct (tm q sq) as [[wq dq qs]|] eqn:Hqs; [|discriminate].
 destruct (tm q (other_sym sq)) as [[zq eq qx]|] eqn:Hqx; [|discriminate].
 destruct (csteps tm anchor c0) as [ca|] eqn:HA; [|discriminate].
 repeat rewrite andb_true_iff in H; destruct H as [[[[H1 H0] H3] H2] Hca].
 apply st_eqb_spec in H1,H0,H3,H2; cbn in H1,H0,H3,H2; subst ps px qs qx.
 assert (Ha : stepn tm anchor InitES = Some (lift ca)).
 { rewrite <- lift_c0; apply csteps_lift; exact HA. }
 assert (Hs : fst (lift ca) = p \/ fst (lift ca) = q).
 { rewrite lift_state; apply orb_true_iff in Hca; destruct Hca as [Hca|Hca];
     apply st_eqb_spec in Hca; auto. }
 split.
 - exact (general_pair_nonhalt tm p q sp sq dp dq ep eq wp wq zp zq
     Hps Hpx Hqs Hqx anchor (lift ca) Ha Hs).
 - exact (general_pair_window tm p q sp sq dp dq ep eq wp wq zp zq
     Hpq Hps Hpx Hqs Hqx anchor (lift ca) Ha Hs).
Qed.

Theorem general_sweep_check_completion : forall tm anchor p q sp sq,
 general_sweep_check tm anchor p q sp sq = true ->
 forall tm', TM_le tm tm' -> NonHalt tm' /\
 forall B, anchor <= B -> WindowBound tm' B (B+2).
Proof.
 intros tm anchor p q sp sq H tm' Hle.
 destruct (general_sweep_check_sound tm anchor p q sp sq H) as [HN HW].
 split; [eapply nonhalt_le; eauto|].
 intros B HB; apply (proj2 (window_bound_completion tm tm' B (B+2) HN Hle)); auto.
Qed.

Print Assumptions general_sweep_check_completion.

Module GeneralSweepRegression.
Definition mixed : TM := fun q s => match q,s with
 | StA,S0 => Some (mkTrans S0 DR StA)
 | StA,S1 => Some (mkTrans S0 DR StB)
 | StB,S0 => Some (mkTrans S1 DL StA)
 | StB,S1 => Some (mkTrans S1 DL StB)
 | _,_ => None end.
Example mixed_symbols_accept : general_sweep_check mixed 0 StA StB S0 S1 = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_scan_symbol_rejects : general_sweep_check mixed 0 StA StB S1 S1 = false.
Proof. vm_compute; reflexivity. Qed.
Example equal_pair_rejects : general_sweep_check mixed 0 StA StA S0 S0 = false.
Proof. vm_compute; reflexivity. Qed.

(** From the blank tape the zero-scan escapes forever. An unconditional
    target-return lemma would be false even though the pair check accepts. *)
Example no_unconditional_return : ~ FutureBeep mixed StB 0.
Proof.
 intros (t & _ & cq & Hr & Hq).
 destruct (zero_scan_future_exit mixed StA StB DR S0 S0 DR ltac:(discriminate)
   eq_refl eq_refl t (snd InitES) cq Hr Hq)
   as (n & j & cq' & Ha & _).
 destruct n; discriminate Ha.
Qed.
Definition spike : Tape := mkTape blank_side S0
 (fun n => match n with 0 => S1 | S _ => S0 end).
Example zero_scan_crosses_on_one :
 fst (match stepn mixed 2 (StA,spike) with Some c => c | None => InitES end) = StB.
Proof. reflexivity. Qed.
Example last_switch_step_is_needed : forall j c,
 j <= 1 -> stepn mixed j (StA,spike) = Some c -> fst c <> StB.
Proof.
 intros [|[|j]] c Hj Hr; try lia;
   cbn [stepn] in Hr; injection Hr as <-; discriminate.
Qed.
End GeneralSweepRegression.
