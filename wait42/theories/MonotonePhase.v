(** SCRATCH: a reflected conditional bound for monotone control phases.
    Failed gates prove nothing. FutureExit is finite and supplies every step;
    no NonHalt hypothesis or unconditional escape assertion is used. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
From BBBWait42 Require Import Sweep.
Import ListNotations.

Definition phase_front_blank d tp := forall n, ahead d tp n = S0.
Lemma phase_front_blank_move : forall d tp w,
 phase_front_blank d tp -> phase_front_blank d (tape_move d w tp).
Proof. intros d tp w H n; rewrite ahead_move; apply H. Qed.

Inductive phase_exit (tm : TM) (P : St -> bool) : ExecState -> nat -> ExecState -> Prop :=
| phase_exit_now : forall c c',
 P (fst c) = true -> step tm c = Some c' -> P (fst c') = false ->
 phase_exit tm P c 1 c'
| phase_exit_later : forall c c1 n c',
 P (fst c) = true -> step tm c = Some c1 -> P (fst c1) = true ->
 phase_exit tm P c1 n c' -> phase_exit tm P c (S n) c'.

Definition PhaseFutureExit tm P c := exists n c', stepn tm n c = Some c' /\ P (fst c') = false.

Lemma phase_exit_run : forall tm P c n c', phase_exit tm P c n c' ->
 1 <= n /\ stepn tm n c = Some c' /\ P (fst c) = true /\ P (fst c') = false.
Proof.
 intros tm P c n c' H; induction H.
 - repeat split; auto; cbn [stepn]; rewrite H0; reflexivity.
 - destruct IHphase_exit as [Hn [Hr [Hi Ho]]].
   repeat split; auto; try lia; cbn [stepn]; rewrite H0; exact Hr.
Qed.

Lemma phase_exit_from_future : forall tm P c,
 P (fst c) = true -> PhaseFutureExit tm P c -> exists n c', phase_exit tm P c n c'.
Proof.
 intros tm P c HI (n & c' & Hr & Ho); revert c HI Hr Ho.
 induction n as [|n IH]; intros c HI Hr Ho.
 - cbn [stepn] in Hr; injection Hr as <-; congruence.
 - cbn [stepn] in Hr; destruct (step tm c) as [c1|] eqn:HS; [|discriminate].
   destruct (P (fst c1)) eqn:HP.
   + destruct (IH c1 HP Hr Ho) as (j & d & HE).
     exists (S j),d; eapply phase_exit_later; eauto.
   + exists 1,c1; eapply phase_exit_now; eauto.
Qed.

Lemma phase_exit_last : forall tm P c n c', phase_exit tm P c n c' ->
 exists cp, stepn tm (n-1) c = Some cp /\ P (fst cp) = true /\ step tm cp = Some c'.
Proof.
 intros tm P c n c' H; induction H.
 - exists c; repeat split; auto.
 - destruct IHphase_exit as (cp & Hr & HI & HS).
   pose proof (phase_exit_run _ _ _ _ _ H2) as [Hn _].
   exists cp; repeat split; auto.
   replace (S n-1) with (S (n-1)) by lia; cbn [stepn]; rewrite H0; exact Hr.
Qed.

Lemma phase_exit_split : forall tm P k c n c',
 phase_exit tm P c n c' -> k < n ->
 exists ck, stepn tm k c = Some ck /\ P (fst ck) = true /\
 phase_exit tm P ck (n-k) c'.
Proof.
 intros tm P k; induction k as [|k IH]; intros c n c' HE Hk.
 - exists c; split; [reflexivity|]. split.
   + exact (proj1 (proj2 (proj2 (phase_exit_run _ _ _ _ _ HE)))).
   + now rewrite Nat.sub_0_r.
 - inversion HE as [c0 z HP HS HO | c0 c1 n0 z HP HS HP1 HX]; subst; [lia|].
   destruct (IH c1 n0 c' HX ltac:(lia)) as (ck & HR & HPk & HXt).
   exists ck; split; [cbn [stepn]; rewrite HS; exact HR|].
   split; [exact HPk|]. replace (S n0-S k) with (n0-k) by lia; exact HXt.
Qed.

Definition phase_dir_eqb d e := match d,e with DL,DL | DR,DR => true | _,_ => false end.
Lemma phase_dir_eqb_spec : forall d e, phase_dir_eqb d e = true -> d=e.
Proof. destruct d,e; simpl; congruence. Qed.
Definition phase_mem q C := existsb (st_eqb q) C.
Lemma phase_mem_spec : forall q C, phase_mem q C = true <-> In q C.
Proof.
 intros q C; unfold phase_mem; rewrite existsb_exists; split.
 - intros (r & HI & HE); apply st_eqb_spec in HE; now subst r.
 - intro HI; exists q; split; [exact HI|apply st_eqb_spec; reflexivity].
Qed.

Fixpoint phase_zero_orbit (tm : TM) (n : nat) (q : St) : list St :=
 q :: match n with
 | 0 => []
 | S k => match tm q S0 with None => [] | Some tr => phase_zero_orbit tm k (t_next tr) end
 end.
Definition phase_trap_check tm P d q C :=
 phase_mem q C && forallb (fun s => if phase_mem s C then
 P s && match tm s S0 with
 | None => true
 | Some tr => phase_mem (t_next tr) C && P (t_next tr) && phase_dir_eqb (t_dir tr) d
 end else true) all_St.

Lemma phase_trap_check_sound : forall tm P d q C,
 phase_trap_check tm P d q C = true ->
 In q C /\ forall s, In s C -> P s = true /\
 match tm s S0 with
 | None => True
 | Some tr => In (t_next tr) C /\ P (t_next tr) = true /\ t_dir tr = d end.
Proof.
 intros tm P d q C H; unfold phase_trap_check in H.
 apply andb_true_iff in H as [HQ HC]; apply phase_mem_spec in HQ; split; [exact HQ|].
 intros s HI; rewrite forallb_forall in HC; specialize (HC s (all_St_complete s)).
 assert (HM : phase_mem s C = true) by (apply phase_mem_spec; exact HI).
 rewrite HM in HC; apply andb_true_iff in HC as [HP HC]; split; [exact HP|].
 destruct (tm s S0) as [tr|]; [|exact I].
 repeat rewrite andb_true_iff in HC; destruct HC as [[HM' HP'] HD].
 apply phase_mem_spec in HM'; apply phase_dir_eqb_spec in HD; auto.
Qed.

Lemma phase_trap_forbids_exit : forall tm P d q C,
 phase_trap_check tm P d q C = true -> forall c n c',
 In (fst c) C -> phase_front_blank d (snd c) -> phase_exit tm P c n c' -> False.
Proof.
 intros tm P d q C HC c n c' HM HB HE.
 destruct (phase_trap_check_sound tm P d q C HC) as [_ HC']; revert HM HB.
 induction HE; intros HM HB; destruct c as [s tp]; cbn in HM,HB.
 - destruct (HC' s HM) as [_ HC0].
   assert (HH : t_head tp = S0) by (exact (HB 0)).
   cbn [step] in H0; rewrite HH in H0.
   destruct (tm s S0) as [[w dir next]|] eqn:HT; [|discriminate].
   injection H0 as <-; destruct HC0 as [_ [HP _]].
   change (P next = true) in HP; change (P next = false) in H1; congruence.
 - destruct (HC' s HM) as [_ HC0].
   assert (HH : t_head tp = S0) by (exact (HB 0)).
   cbn [step] in H0; rewrite HH in H0.
   destruct (tm s S0) as [[w dir next]|] eqn:HT; [|discriminate].
   injection H0 as <-; destruct HC0 as [HN [_ HD]]; cbn in HD; subst dir.
   apply IHHE; [exact HN|apply phase_front_blank_move; exact HB].
Qed.

Fixpoint phase_blank_guard (tm : TM) (P : St -> bool) (d : Dir) (fuel : nat) (q : St) : bool :=
 if P q then match fuel with
 | 0 => phase_trap_check tm P d q (phase_zero_orbit tm 4 q)
 | S k => match tm q S0 with
          | None => true
          | Some tr => phase_blank_guard tm P d k (t_next tr) end
 end else true.

Definition phase_internal_ok (tm : TM) (P : St -> bool) (d : Dir) := forallb (fun q => if P q then
 forallb (fun a => match tm q a with
 | None => true
 | Some tr => if P (t_next tr) then phase_dir_eqb (t_dir tr) d else true
 end) [S0;S1] else true) all_St.

Lemma phase_internal_ok_sound : forall tm P d,
 phase_internal_ok tm P d = true -> forall q a tr,
 P q = true -> tm q a = Some tr -> P (t_next tr) = true -> t_dir tr = d.
Proof.
 intros tm P d H q a tr HP HT HN; unfold phase_internal_ok in H.
 rewrite forallb_forall in H; specialize (H q (all_St_complete q)); rewrite HP in H.
 rewrite forallb_forall in H; specialize (H a ltac:(destruct a; simpl; auto)).
 rewrite HT,HN in H; now apply phase_dir_eqb_spec in H.
Qed.

Definition phase_check tm P d := phase_internal_ok tm P d &&
 forallb (fun q => if P q then phase_blank_guard tm P d 4 q else true) all_St.

Lemma phase_blank_exit_bound : forall tm P d,
 phase_internal_ok tm P d = true -> forall fuel c n c',
 phase_blank_guard tm P d fuel (fst c) = true ->
 phase_front_blank d (snd c) -> phase_exit tm P c n c' -> n <= fuel.
Proof.
 intros tm P d HI fuel; induction fuel as [|fuel IH]; intros [s tp] n c' HG HB HE.
 - cbn [phase_blank_guard fst] in HG.
   pose proof (phase_exit_run _ _ _ _ _ HE) as [_ [_ [HP _]]].
   change (P s = true) in HP; rewrite HP in HG.
   exfalso; eapply phase_trap_forbids_exit; [exact HG| |exact HB|exact HE].
   apply phase_mem_spec; exact (proj1 (andb_prop _ _ HG)).
 - inversion HE as [c0 z HP HS HO | c0 c1 n0 z HP HS HP1 HX]; subst.
   + lia.
   + assert (HH : t_head tp = S0) by (exact (HB 0)).
     cbn [phase_blank_guard fst] in HG; change (P s = true) in HP; rewrite HP in HG.
     cbn [step] in HS; rewrite HH in HS.
     destruct (tm s S0) as [[w dir next]|] eqn:HT; [|discriminate].
     injection HS as <-.
     assert (HD : dir = d).
     { exact (phase_internal_ok_sound tm P d HI s S0 (mkTrans w dir next) HP HT HP1). }
     subst dir.
     assert (HN : n0 <= fuel).
     { apply (IH (next,tape_move d w tp) n0 c'); [exact HG|apply phase_front_blank_move; exact HB|exact HX]. }
     lia.
Qed.

Lemma phase_exit_prefix_inside : forall tm P c n c', phase_exit tm P c n c' ->
 forall k ck, k < n -> stepn tm k c = Some ck -> P (fst ck) = true.
Proof.
 intros tm P c n c' HE; induction HE; intros k ck Hk HR.
 - assert (k=0) by lia; subst k; cbn [stepn] in HR; injection HR as <-; exact H.
 - destruct k as [|k].
   + cbn [stepn] in HR; injection HR as <-; exact H.
   + cbn [stepn] in HR; rewrite H0 in HR; eapply IHHE; eauto; lia.
Qed.

Lemma phase_exit_before_outside : forall tm P c n c', phase_exit tm P c n c' ->
 forall k ck, stepn tm k c = Some ck -> P (fst ck) = false ->
 n <= k /\ stepn tm (k-n) c' = Some ck.
Proof.
 intros tm P c n c' HE k ck HR HO.
 assert (Hn : n <= k).
 { destruct (le_dec n k) as [Hle|Hle]; [exact Hle|].
   pose proof (phase_exit_prefix_inside tm P c n c' HE k ck ltac:(lia) HR); congruence. }
 split; [exact Hn|].
 destruct (phase_exit_run tm P c n c' HE) as [_ [HN _]].
 replace k with (n+(k-n)) in HR by lia; rewrite stepn_add,HN in HR; exact HR.
Qed.

From BBBWait42 Require Import AheadShift.

Theorem phase_check_exit_bound : forall tm P d B c n c',
 phase_check tm P d = true -> stepn tm B InitES = Some c ->
 phase_exit tm P c n c' -> n <= B+5.
Proof.
 intros tm P d B c n c' HG HB HE.
 destruct (le_dec n (S B)) as [Hshort|Hlong]; [lia|].
 unfold phase_check in HG; apply andb_true_iff in HG as [HI HG].
 destruct (phase_exit_split tm P (S B) c n c' HE ltac:(lia))
   as (ck & HK & HPK & HEK).
 assert (HFB : phase_front_blank d (snd ck)).
 { apply (phase_prefix_forwardblank tm (fun s => P s = true) d
     (phase_internal_ok_sound tm P d HI) B c ck).
   - exact (blank_radius_from_blank tm B c HB).
   - exact HK.
   - intros j cj Hj HR; exact (phase_exit_prefix_inside tm P c n c' HE j cj ltac:(lia) HR). }
 rewrite forallb_forall in HG; specialize (HG (fst ck) (all_St_complete (fst ck))).
 rewrite HPK in HG.
 pose proof (phase_blank_exit_bound tm P d HI 4 ck (n-S B) c' HG HFB HEK).
 lia.
Qed.

Theorem phase_check_conditional_exit : forall tm P d B c,
 phase_check tm P d = true -> stepn tm B InitES = Some c ->
 P (fst c) = true -> PhaseFutureExit tm P c ->
 exists n c', n <= B+5 /\ phase_exit tm P c n c'.
Proof.
 intros tm P d B c HC HB HP HF.
 destruct (phase_exit_from_future tm P c HP HF) as (n & c' & HE).
 exists n,c'; split; [eapply phase_check_exit_bound; eauto|exact HE].
Qed.

(** The selected exit lies before any supplied outside-target witness, so
    phase composition retains the original future target continuation. *)
Theorem phase_check_exit_before : forall tm P d B c N target,
 phase_check tm P d = true -> stepn tm B InitES = Some c ->
 P (fst c) = true -> stepn tm N c = Some target -> P (fst target) = false ->
 exists n c', n <= B+5 /\ n <= N /\ phase_exit tm P c n c' /\
 stepn tm (N-n) c' = Some target.
Proof.
 intros tm P d B c N target HC HB HP HR HO.
 destruct (phase_check_conditional_exit tm P d B c HC HB HP
   (ex_intro _ N (ex_intro _ target (conj HR HO)))) as (n & c' & Hn & HE).
 destruct (phase_exit_before_outside tm P c n c' HE N target HR HO) as [HN HT].
 exists n,c'; auto.
Qed.

Print Assumptions phase_check_exit_bound.
Print Assumptions phase_check_exit_before.

Module MonotonePhaseRegression.
Definition three_phase s := match s with StA|StB|StC => true | StD => false end.
Definition terminal : TM := fun q a => match q,a with
 | StA,S0 => Some (mkTrans S0 DR StB)
 | StB,S0 => Some (mkTrans S0 DR StC)
 | StC,S0 => Some (mkTrans S1 DL StD)
 | StD,_ => None
 | _,S1 => Some (mkTrans S1 DL StD) end.
Definition endpoint := (StD,tape_move DL S1
 (tape_move DR S0 (tape_move DR S0 (snd InitES)))).
Example terminal_gate : phase_check terminal three_phase DR = true.
Proof. vm_compute; reflexivity. Qed.
Example terminal_exit_preserves_witness :
 exists n c', n <= 5 /\ n <= 3 /\ phase_exit terminal three_phase InitES n c' /\
 stepn terminal (3-n) c' = Some endpoint.
Proof.
 exact (phase_check_exit_before terminal three_phase DR 0 InitES 3 endpoint
   terminal_gate eq_refl eq_refl eq_refl eq_refl).
Qed.
Example terminal_halts : ~ NonHalt terminal.
Proof. intro H; apply (H 4); reflexivity. Qed.

Definition pair s := match s with StA|StB => true | _ => false end.
Definition trap : TM := fun q a => match q,a with
 | StA,S0 => Some (mkTrans S1 DR StB)
 | StB,S0 => Some (mkTrans S1 DR StA)
 | _,_ => Some (mkTrans S0 DL StD) end.
Example closed_blank_orbit_accepts : phase_check trap pair DR = true.
Proof. vm_compute; reflexivity. Qed.
Example tampered_closed_subset_rejects : phase_trap_check trap pair DR StA [StA] = false.
Proof. vm_compute; reflexivity. Qed.
Example blank_orbit_does_not_escape : ~ PhaseFutureExit trap pair InitES.
Proof.
 intro HF; destruct (phase_exit_from_future trap pair InitES eq_refl HF) as (n & c' & HE).
 apply (phase_trap_forbids_exit trap pair DR StA (phase_zero_orbit trap 4 StA)
   eq_refl InitES n c' ltac:(left; reflexivity)); [|exact HE].
 intros k; destruct k; reflexivity.
Qed.
Definition mixed : TM := fun q _ => match q with
 | StA => Some (mkTrans S0 DR StB)
 | StB => Some (mkTrans S0 DL StA)
 | _ => None end.
Example mixed_internal_directions_reject : phase_check mixed pair DR = false.
Proof. vm_compute; reflexivity. Qed.
End MonotonePhaseRegression.
