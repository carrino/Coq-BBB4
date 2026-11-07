(** Finite inclusive observation windows for every completion.
    All-state observations need no nonhalting or final-configuration premise.
    The tail alternative requires an actual endpoint and a total closed set. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec BinaryScan ControlRank.
Import ListNotations.

Record state_bits := Bits { bitA:bool; bitB:bool; bitC:bool; bitD:bool }.
Definition no_bits := Bits false false false false.
Definition bit_get q b := match q with StA=>bitA b|StB=>bitB b|StC=>bitC b|StD=>bitD b end.
Definition bit_mark q b := Bits (bitA b || st_eqb q StA) (bitB b || st_eqb q StB)
 (bitC b || st_eqb q StC) (bitD b || st_eqb q StD).
Lemma bit_get_mark : forall q s b, bit_get q (bit_mark s b) = bit_get q b || st_eqb s q.
Proof. intros q s [a b c d]; destruct q; reflexivity. Qed.
Definition observation_body tm (s:option cconf * state_bits) :=
 match s with (Some c,b) => (cstep tm c,bit_mark (fst c) b) | (None,b)=>(None,b) end.
Definition observation_scan tm w c := N.iter w (observation_body tm) (Some c,no_bits).
Definition observation_window tm B w :=
 match cstepsN tm B c0 with
 | None => (None,no_bits)
 | Some c => let '(oc,b):=observation_scan tm w c in
   (oc,match oc with Some e=>bit_mark (fst e) b|None=>b end)
 end.

Lemma observation_fst : forall tm n oc b,
 fst (Nat.iter n (observation_body tm) (oc,b)) =
 match oc with Some c=>csteps tm n c|None=>None end.
Proof.
 intros tm n; induction n; intros oc b; [destruct oc; reflexivity|].
 rewrite Nat.iter_succ_r; destruct oc as [c|]; cbn [observation_body]; rewrite IHn.
 - simpl; destruct (cstep tm c); reflexivity.
 - reflexivity.
Qed.
Lemma observation_snd : forall tm n oc b q,
 bit_get q (snd (Nat.iter n (observation_body tm) (oc,b))) = bit_get q b ||
 match oc with Some c=>visits tm (fun c=>st_eqb (fst c) q) n c|None=>false end.
Proof.
 intros tm n; induction n; intros oc b q.
 - destruct oc; simpl; now rewrite orb_false_r.
 - rewrite Nat.iter_succ_r; destruct oc as [c|]; cbn [observation_body]; rewrite IHn.
   + rewrite bit_get_mark; cbn [visits]; destruct (cstep tm c); rewrite ?orb_assoc; reflexivity.
   + now rewrite orb_false_r.
Qed.
Lemma visits_sound : forall tm hit n c,
 visits tm hit n c=true -> exists i d, i<n /\ csteps tm i c=Some d /\ hit d=true.
Proof.
 intros tm hit n; induction n as [|n IH]; intros c H; [discriminate|].
 cbn [visits] in H; apply orb_true_iff in H as [H|H].
 - exists 0,c; repeat split; auto; lia.
 - destruct (cstep tm c) as [e|] eqn:HE; [|discriminate].
   destruct (IH e H) as (i & d & Hi & HR & HH).
   exists (S i),d; split; [lia|]; split; [cbn [csteps]; rewrite HE; exact HR|exact HH].
Qed.

Theorem observation_window_witness : forall tm B w oc bits,
 observation_window tm B w=(oc,bits) -> forall q, bit_get q bits=true ->
 exists i d, i<=N.to_nat w /\ csteps tm (N.to_nat B+i) c0=Some d /\ fst d=q.
Proof.
 intros tm B w oc bits HW q HQ; unfold observation_window in HW; rewrite cstepsN_nat in HW.
 destruct (csteps tm (N.to_nat B) c0) as [c|] eqn:HB.
 - destruct (observation_scan tm w c) as [oe b] eqn:HS; injection HW as <- <-.
   pose proof (observation_snd tm (N.to_nat w) (Some c) no_bits q) as HV.
   pose proof (observation_fst tm (N.to_nat w) (Some c) no_bits) as HF.
   rewrite <- N2Nat.inj_iter in HV,HF; fold (observation_scan tm w c) in HV,HF.
   rewrite HS in HV,HF; cbn [fst snd] in HV,HF.
   assert (HZ : bit_get q no_bits=false) by (destruct q; reflexivity).
   rewrite HZ in HV; cbn [orb] in HV.
   assert (Hprefix : bit_get q b=true -> exists i d, i<=N.to_nat w /\
     csteps tm (N.to_nat B+i) c0=Some d /\ fst d=q).
   { intro HP; rewrite HP in HV; symmetry in HV.
     destruct (visits_sound tm _ _ c HV) as (i & d & Hi & HR & HH).
     apply st_eqb_spec in HH; exists i,d; split; [lia|]; split; [rewrite csteps_add,HB; exact HR|exact HH]. }
   destruct oe as [e|].
   + rewrite bit_get_mark in HQ; apply orb_true_iff in HQ as [HQ|HQ]; [apply Hprefix; exact HQ|].
     apply st_eqb_spec in HQ; exists (N.to_nat w),e; split; [lia|].
     split; [rewrite csteps_add,HB; symmetry; exact HF|exact HQ].
   + apply Hprefix; exact HQ.
 - injection HW as <- <-; destruct q; discriminate HQ.
Qed.

Lemma observation_window_endpoint : forall tm B w e bits,
 observation_window tm B w=(Some e,bits) ->
 csteps tm (N.to_nat B+N.to_nat w) c0=Some e.
Proof.
 intros tm B w e bits HW; unfold observation_window in HW; rewrite cstepsN_nat in HW.
 destruct (csteps tm (N.to_nat B) c0) as [c|] eqn:HB; [|discriminate].
 destruct (observation_scan tm w c) as [oe b] eqn:HS; injection HW as <- Heq.
 pose proof (observation_fst tm (N.to_nat w) (Some c) no_bits) as HF.
 rewrite <- N2Nat.inj_iter in HF; fold (observation_scan tm w c) in HF.
 rewrite HS in HF; cbn [fst] in HF; rewrite csteps_add,HB; symmetry; exact HF.
Qed.

Lemma observation_completion_beep : forall tm tm' B w oc bits q,
 TM_le tm tm' -> observation_window tm B w=(oc,bits) -> bit_get q bits=true ->
 BeepWindow tm' q (N.to_nat B) (N.to_nat w).
Proof.
 intros tm tm' B w oc bits q Hle HW HQ.
 destruct (observation_window_witness tm B w oc bits HW q HQ) as (i & d & Hi & HR & Hq).
 exists (N.to_nat B+i); repeat split; try lia.
 exists (lift d); split.
 - eapply TM_le_stepn; [exact Hle|rewrite <- lift_c0; apply csteps_lift; exact HR].
 - destruct d as [s [[l h] r]]; exact Hq.
Qed.

Definition all_bits bits := forallb (fun q=>bit_get q bits) all_St.
Definition tail_observed tm inv bits (endpoint : cconf) :=
 inv (fst endpoint) && cr_closed_ok tm inv &&
 forallb (fun q=>if inv q then bit_get q bits else true) all_St.
Definition finite_observation_check tm inv B w :=
 let '(oc,bits):=observation_window tm B w in
 all_bits bits || match oc with Some e=>tail_observed tm inv bits e|None=>false end.

Lemma observation_tail_closed : forall tm tm' inv,
 TM_le tm tm' -> cr_closed_ok tm inv=true -> forall n c c',
 inv (fst c)=true -> stepn tm' n c=Some c' -> inv (fst c')=true.
Proof.
 intros tm tm' inv Hle HC n; induction n as [|n IH]; intros [s tp] c' HI HR.
 - cbn [stepn] in HR; injection HR as <-; exact HI.
 - destruct (cr_closed_step tm inv HC s (t_head tp) HI) as (tr & HT & HN).
   assert (HT' : tm' s (t_head tp)=Some tr) by (destruct (Hle s (t_head tp)) as [Hbad|Hgood]; congruence).
   cbn [stepn step] in HR; rewrite HT' in HR; apply (IH (t_next tr,tape_move (t_dir tr) (t_write tr) tp) c'); [exact HN|exact HR].
Qed.

Theorem finite_observation_check_completion : forall tm inv B w,
 finite_observation_check tm inv B w=true -> forall tm', TM_le tm tm' ->
 WindowBound tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv B w HC tm' Hle q HF.
 unfold finite_observation_check in HC; destruct (observation_window tm B w) as [oc bits] eqn:HW.
 apply orb_true_iff in HC as [HA|HT].
 - unfold all_bits in HA; rewrite forallb_forall in HA.
   eapply observation_completion_beep; [exact Hle|exact HW|apply HA; apply all_St_complete].
 - destruct oc as [e|]; [|discriminate]; unfold tail_observed in HT.
   repeat rewrite andb_true_iff in HT; destruct HT as [[HI HC] HO].
   destruct HF as (t & Ht & cq & HR & Hq).
   destruct (le_dec t (N.to_nat B+N.to_nat w)) as [Hearly|Hlate].
   + exists t; repeat split; auto; exists cq; auto.
   + pose proof (observation_window_endpoint tm B w e bits HW) as HE.
     assert (HE' : stepn tm' (N.to_nat B+N.to_nat w) InitES=Some (lift e)).
     { eapply TM_le_stepn; [exact Hle|rewrite <- lift_c0; apply csteps_lift; exact HE]. }
     replace t with ((N.to_nat B+N.to_nat w)+(t-(N.to_nat B+N.to_nat w))) in HR by lia.
     rewrite stepn_add,HE' in HR.
     assert (HI' : inv (fst (lift e))=true) by (destruct e as [s [[l h] r]]; exact HI).
     pose proof (observation_tail_closed tm tm' inv Hle HC _ _ _ HI' HR) as HQ.
     rewrite Hq in HQ; rewrite forallb_forall in HO; specialize (HO q (all_St_complete q)); rewrite HQ in HO.
     eapply observation_completion_beep; eauto.
Qed.
Print Assumptions finite_observation_check_completion.

(** Every entry has its own checked finite window. The binary gate checks
    that this local width fits the requested common width before widening. *)
Record observation_case := mkObservationCase {
 observation_machine : TM;
 observation_inv : St -> bool;
 observation_width : N
}.
Definition observation_batch_check (entries : list observation_case) (B W : N) :=
 forallb (fun e => N.leb (observation_width e) W &&
   finite_observation_check (observation_machine e) (observation_inv e) B
     (observation_width e)) entries.

Theorem observation_batch_completion : forall entries B W,
 observation_batch_check entries B W = true ->
 forall e, In e entries -> forall tm', TM_le (observation_machine e) tm' ->
 WindowBound tm' (N.to_nat B) (N.to_nat W).
Proof.
 intros entries B W HC e HI tm' Hle.
 unfold observation_batch_check in HC; rewrite forallb_forall in HC.
 specialize (HC e HI); apply andb_true_iff in HC as [HW HC].
 apply N.leb_le in HW.
 eapply window_mono.
 - assert (Hnat : N.to_nat (observation_width e) <= N.to_nat W) by lia.
   exact Hnat.
 - exact (finite_observation_check_completion (observation_machine e)
     (observation_inv e) B (observation_width e) HC tm' Hle).
Qed.

Print Assumptions observation_batch_completion.
