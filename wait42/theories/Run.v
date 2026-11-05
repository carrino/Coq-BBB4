(** A small executable waiting census pilot. A bounded walk preserves a
    certified residual obligation; this file makes no claim that it empties. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec CTape GTape Mirror Closure PosEnc.
From BBB4.Checkers Require Import NGram ExactClosure.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport Periodic Ranked Census.
Import ListNotations.

(** The verified halt-search routine from BBB4.Census.Decide, reproduced
    locally to avoid importing its unrelated decider tiers. *)
Fixpoint find_halt (tm : TM) (gas k : nat) (c : cconf)
  : option (nat * St * Sym) :=
  match gas with
  | 0 => None
  | S g =>
      match cstep tm c with
      | Some c' => find_halt tm g (S k) c'
      | None => let '(q, (l, h, r)) := c in Some (k, q, h)
      end
  end.

Lemma cstep_none : forall tm q l h r,
  cstep tm (q, (l, h, r)) = None -> tm q h = None.
Proof.
  intros tm q l h r H. unfold cstep in H.
  destruct (tm q h) as [tr|]; [discriminate | reflexivity].
Qed.

Lemma find_halt_sound : forall tm gas k c n s i,
  csteps tm k c0 = Some c ->
  find_halt tm gas k c = Some (n, s, i) ->
  exists tp, stepn tm n InitES = Some (s, tp) /\ t_head tp = i /\ tm s i = None.
Proof.
  intros tm.
  induction gas; intros k c n s i Hk H; simpl in H; [discriminate|].
  destruct (cstep tm c) as [c'|] eqn:E.
  - apply (IHgas (S k) c'); [|assumption].
    replace (S k) with (k + 1) by lia.
    rewrite csteps_add, Hk, csteps_1. exact E.
  - destruct c as [q [[l h] r]].
    injection H as <- <- <-.
    exists (lift_tape (l, h, r)).
    pose proof (csteps_lift tm k c0 (q, (l, h, r)) Hk) as Hl.
    rewrite lift_c0 in Hl.
    split; [exact Hl|].
    split; [reflexivity|].
    exact (cstep_none tm q l h r E).
Qed.


Lemma find_halt_steps_bound : forall tm gas k c n q i,
 find_halt tm gas k c = Some (n,q,i) -> k <= n < k+gas.
Proof.
 intros tm gas; induction gas; intros k c n q i H; simpl in H; [discriminate|].
 destruct (cstep tm c) as [c'|] eqn:EC.
 - specialize (IHgas (S k) c' n q i H); lia.
 - destruct c as [s [[l h] r]]; injection H as <- <- <-; lia.
Qed.

Definition pilot_width : nat := 4096.
Definition pilot_halt_gas : nat := 130.

Lemma pilot_halt_gas_le_cutoff : pilot_halt_gas <= champion_score.
Proof.
 change (N.to_nat 130 <= N.to_nat 32779478).
 apply Nat.compare_le_iff; rewrite <- N2Nat.inj_compare; discriminate.
Qed.

Lemma pilot_binary_anchor_le : forall a,
 (a <= 32779478)%N -> N.to_nat a <= champion_score.
Proof.
 intros a HA; unfold champion_score; apply Nat.compare_le_iff;
 rewrite <- N2Nat.inj_compare; apply N.compare_le_iff; exact HA.
Qed.
Local Opaque champion_score.

(** Closed n-gram tails supply nonhalting directly, without an extra
    qualitative checker pass or a simulation to the large cutoff. *)
Lemma ranked_tail_nonhalt : forall tm n ls rs cc Sl ranks t w,
 1 <= n -> csteps tm t c0 = Some cc ->
 ngram_ranked_tail_ok tm n ls rs cc Sl ranks w = true -> NonHalt tm.
Proof.
 intros tm n ls rs cc Sl ranks t w Hn HA Hgate k Hnone.
 unfold ngram_ranked_tail_ok in Hgate.
 apply andb_true_iff in Hgate as [Hgate Hrank].
 apply andb_true_iff in Hgate as [Hgate Hcl].
 apply andb_true_iff in Hgate as [Hseed Hmem].
 assert (Hcov : ng_covers n ls rs (ng_start n cc) (lift cc)).
 { apply ng_start_covers; exact Hseed. }
 assert (HIn : In (ng_start n cc) Sl).
 { apply (mem_In cconf cconf_enc cconf_enc_inj); exact Hmem. }
 assert (Hsucc : forall a c, ng_covers n ls rs a c ->
  match ng_succs tm ls rs a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ ng_covers n ls rs a' c'
  | Some _, None => False | None, _ => True end).
 { intros a c HC; apply ng_succs_sound; assumption. }
 destruct (closure_invariant tm cconf cconf_enc (ng_succs tm ls rs)
   (ng_covers n ls rs) cconf_enc_inj Hsucc Sl Hcl (ng_start n cc)
   (lift cc) HIn Hcov k) as (c'&a'&HK&_).
 assert (HF : stepn tm (t+k) InitES = Some c').
 { rewrite stepn_add, <- lift_c0, (csteps_lift tm t c0 cc HA); exact HK. }
 replace (t+k) with (k+t) in HF by lia.
 rewrite stepn_add, Hnone in HF; discriminate.
Qed.

Lemma ranked_search_nonhalt : forall tm n t fuel rounds w,
 ngram_ranked_search tm n t fuel rounds w = true -> NonHalt tm.
Proof.
 intros tm n t fuel rounds w H.
 unfold ngram_ranked_search in H; apply andb_true_iff in H as [Hn H].
 apply Nat.leb_le in Hn.
 destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
 cbv beta iota zeta in H.
 match type of H with
 | (let '(_, _) := ?G in _) = true => destruct G as [ls rs] eqn:Eg
 end.
 cbv beta iota zeta in H.
 match type of H with
 | (match ?G with Some _ => _ | None => _ end) = true =>
     destruct G as [Sl|] eqn:Ecl
 end; [|discriminate].
 eapply ranked_tail_nonhalt; eauto.
Qed.

Local Opaque ngram_ranked_search.

Definition pilot_profiles : list (N * nat * nat) :=
 [(0%N,1,0); (0%N,2,0); (0%N,4,0); (8%N,2,2);
  (32%N,16,8); (128%N,64,32)].

Definition pilot_profile_ok tm (profile : N * nat * nat) : bool :=
 let '(a,P,W) := profile in
 (a <=? 32779478)%N && (P-1 <=? pilot_width) &&
 (periodic_check tm a P W || periodic_check (mirror_tm tm) a P W).
Definition pilot_periodic tm := existsb (pilot_profile_ok tm) pilot_profiles.

Lemma pilot_profile_sound : forall tm profile,
 pilot_profile_ok tm profile = true ->
 NonHalt tm /\ WindowBound tm champion_score pilot_width.
Proof.
 intros tm [[a P] W] H; unfold pilot_profile_ok in H.
 apply andb_true_iff in H as [Hguard HC].
 apply andb_true_iff in Hguard as [HA HP].
 apply N.leb_le in HA; apply Nat.leb_le in HP.
 assert (Hcut : N.to_nat a <= champion_score).
 { apply pilot_binary_anchor_le; exact HA. }
 apply orb_true_iff in HC as [HC|HC].
 - split; [eapply periodic_check_nonhalt; eauto|].
   eapply window_mono; [exact HP|].
   eapply periodic_check_state_sound; eauto.
 - split.
   + apply mirror_nonhalt; eapply periodic_check_nonhalt; eauto.
   + eapply window_mono; [exact HP|].
     exact (proj1 (periodic_check_sound_L tm a P W HC champion_score Hcut)).
Qed.
Lemma pilot_periodic_sound : forall tm, pilot_periodic tm = true ->
 NonHalt tm /\ WindowBound tm champion_score pilot_width.
Proof.
 intros tm H; unfold pilot_periodic in H; apply existsb_exists in H.
 destruct H as (p&_&HP); eapply pilot_profile_sound; exact HP.
Qed.

Definition pilot_ranked tm : bool :=
 ngram_ranked_search tm 1 0 16 2 pilot_width ||
 ngram_ranked_search tm 2 32 16 2 pilot_width.
Lemma pilot_ranked_sound : forall tm B, pilot_halt_gas <= B ->
 pilot_ranked tm = true -> NonHalt tm /\ WindowBound tm B pilot_width.
Proof.
 intros tm B HB H; unfold pilot_ranked in H; apply orb_true_iff in H as [H|H]; split.
 - exact (ranked_search_nonhalt tm 1 0 16 2 pilot_width H).
 - exact (ngram_ranked_search_sound tm 1 0 16 2 pilot_width B (Nat.le_0_l _) H).
 - exact (ranked_search_nonhalt tm 2 32 16 2 pilot_width H).
 - apply (ngram_ranked_search_sound tm 2 32 16 2 pilot_width B); [|exact H].
   eapply Nat.le_trans; [|exact HB]. unfold pilot_halt_gas; lia.
Qed.

Definition pilot_decider (tm : TM) : QHResult :=
 match find_halt tm pilot_halt_gas 0 c0 with
 | Some (_,q,i) => R_Halt q i
 | None => if pilot_periodic tm then R_Leaf
           else if pilot_ranked tm then R_Leaf else R_Unknown
 end.

Theorem pilot_decider_wf :
 Census.QHDecider_WF champion_score pilot_width [] pilot_decider.
Proof.
 intro tm; unfold pilot_decider.
 destruct (find_halt tm pilot_halt_gas 0 c0) as [[[n q] i]|] eqn:EH.
 - destruct (find_halt_sound tm pilot_halt_gas 0 c0 n q i eq_refl EH)
     as (tp&HT&HI&HH).
   exists n,tp; repeat split; auto.
   pose proof (find_halt_steps_bound tm pilot_halt_gas 0 c0 n q i EH) as HB.
   eapply Nat.le_trans; [|exact pilot_halt_gas_le_cutoff]; lia.
 - destruct (pilot_periodic tm) eqn:EP.
   + apply pilot_periodic_sound; exact EP.
   + destruct (pilot_ranked tm) eqn:ER; [apply pilot_ranked_sound; [exact pilot_halt_gas_le_cutoff|exact ER]|exact I].
Qed.

Definition pilot_empty_tm : TM := fun _ _ => None.
Definition pilot_root : TNF_Node := mkNode pilot_empty_tm (Some StB).
Definition pilot_initial : SearchQueue := SearchQueue_init pilot_root.
Definition pilot_walk (rounds : nat) : SearchQueue :=
 SearchQueue_upds pilot_initial pilot_decider rounds.

Lemma pilot_root_wf : Node_WF pilot_root.
Proof.
 unfold Node_WF, pilot_root; simpl; intro u; split.
 - intros (_&_&HA); destruct u; simpl; congruence || lia.
 - intro Hu; repeat split.
   + intros q s tr H; discriminate.
   + intro Hc; subst u; simpl in Hu; lia.
Qed.
Theorem pilot_initial_wf :
 Census.SearchQueue_WF champion_score pilot_width [] pilot_initial pilot_root.
Proof. apply Census.SearchQueue_init_spec; exact pilot_root_wf. Qed.
Theorem pilot_walk_wf : forall n,
 Census.SearchQueue_WF champion_score pilot_width [] (pilot_walk n) pilot_root.
Proof. intro n; apply Census.SearchQueue_upds_spec; [exact pilot_initial_wf|exact pilot_decider_wf]. Qed.

(** The unresolved front/back lists are explicit residual obligations. *)
Theorem pilot_front_covers_all : forall n,
 (forall x, In x (fst (pilot_walk n) ++ snd (pilot_walk n)) ->
   Census.NodeDecided champion_score pilot_width [] (node_tm x)) ->
 forall tm, Census.Decided champion_score pilot_width [] tm.
Proof.
 intros n H tm.
 pose proof (pilot_walk_wf n) as HQ.
 destruct (pilot_walk n) as [front back]; simpl in HQ,H.
 destruct HQ as [_ Hcover].
 apply (Hcover H tm); apply TM_le_TM0; reflexivity.
Qed.

Example pilot_root_halt : pilot_decider pilot_empty_tm = R_Halt StA S0.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions pilot_decider_wf.
Print Assumptions pilot_front_covers_all.

Lemma pilot_no_deferred : forall tm, ~ Deferred [] tm.
Proof.
 intros tm H; induction H; [contradiction|exact IHDeferred|exact IHDeferred].
Qed.
Theorem pilot_front_wait_bound : forall n,
 (forall x, In x (fst (pilot_walk n) ++ snd (pilot_walk n)) ->
   Census.NodeDecided champion_score pilot_width [] (node_tm x)) ->
 WaitBound champion_score pilot_width.
Proof.
 intros n H tm; destruct (pilot_front_covers_all n H tm) as [HW|HD];
 [exact HW|exfalso; exact (pilot_no_deferred tm HD)].
Qed.
Corollary pilot_if_empty : forall n, pilot_walk n = ([],[]) ->
 WaitBound champion_score pilot_width.
Proof.
 intros n H; apply (pilot_front_wait_bound n); rewrite H; simpl; intros x HX; contradiction.
Qed.

(** Cheap leaves retain their small checked windows while unresolved
    families may later be discharged at a larger candidate width.
    The executable decider and the computed walk are unchanged. *)
Theorem pilot_decider_wf_at_width : forall w, pilot_width <= w ->
 Census.QHDecider_WF champion_score w [] pilot_decider.
Proof.
 intros w Hwidth tm; pose proof (pilot_decider_wf tm) as H.
 destruct (pilot_decider tm); [exact H| | | |exact H|exact H].
 all: destruct H as [Hnh HW]; split; [exact Hnh|].
 all: eapply window_mono; [exact Hwidth|exact HW].
Qed.
Theorem pilot_walk_wf_at_width : forall w, pilot_width <= w -> forall n,
 Census.SearchQueue_WF champion_score w [] (pilot_walk n) pilot_root.
Proof.
 intros w Hw n; apply Census.SearchQueue_upds_spec.
 - apply Census.SearchQueue_init_spec; exact pilot_root_wf.
 - apply pilot_decider_wf_at_width; exact Hw.
Qed.
Theorem pilot_front_covers_all_at_width : forall w, pilot_width <= w -> forall n,
 (forall x, In x (fst (pilot_walk n) ++ snd (pilot_walk n)) ->
   Census.NodeDecided champion_score w [] (node_tm x)) ->
 forall tm, Census.Decided champion_score w [] tm.
Proof.
 intros w Hw n H tm.
 pose proof (pilot_walk_wf_at_width w Hw n) as HQ.
 destruct (pilot_walk n) as [front back]; simpl in HQ,H.
 destruct HQ as [_ Hcover].
 apply (Hcover H tm); apply TM_le_TM0; reflexivity.
Qed.
Theorem pilot_front_wait_bound_at_width : forall w, pilot_width <= w -> forall n,
 (forall x, In x (fst (pilot_walk n) ++ snd (pilot_walk n)) ->
   Census.NodeDecided champion_score w [] (node_tm x)) ->
 WaitBound champion_score w.
Proof.
 intros w Hw n H tm.
 destruct (pilot_front_covers_all_at_width w Hw n H tm) as [HW|HD];
 [exact HW|exfalso; exact (pilot_no_deferred tm HD)].
Qed.
Corollary pilot_if_empty_at_width : forall w, pilot_width <= w -> forall n,
 pilot_walk n = ([],[]) -> WaitBound champion_score w.
Proof.
 intros w Hw n H; apply (pilot_front_wait_bound_at_width w Hw n).
 rewrite H; simpl; intros x HX; contradiction.
Qed.
Print Assumptions pilot_front_wait_bound_at_width.
