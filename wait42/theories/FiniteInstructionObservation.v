(** Finite inclusive instruction observations for every TM_le completion.
    The all-eight branch needs neither nonhalting nor a final configuration.
    The tail branch requires a real endpoint in a total closed STATE set;
    BOTH read-symbol slots of every state in that set must be observed.
    In particular, undefined transitions never establish closedness. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec BinaryScan ControlRank FiniteObservation.
Import ListNotations.

Definition cinstr_of (c : cconf) : Instr :=
 let '(s,(_,h,_)) := c in (s,h).
Lemma cinstr_of_lift : forall c, instr_of (lift c) = cinstr_of c.
Proof. intros [s [[l h] r]]; reflexivity. Qed.

(** Eight physical Boolean fields, one per (state, read-symbol) slot. *)
Record instruction_bits := InstructionBits {
 instruction_bitA0 : bool; instruction_bitA1 : bool;
 instruction_bitB0 : bool; instruction_bitB1 : bool;
 instruction_bitC0 : bool; instruction_bitC1 : bool;
 instruction_bitD0 : bool; instruction_bitD1 : bool
}.
Definition no_instruction_bits := InstructionBits false false false false false false false false.
Definition instruction_bit_get (q : Instr) b := match q with
 | (StA,S0) => instruction_bitA0 b | (StA,S1) => instruction_bitA1 b
 | (StB,S0) => instruction_bitB0 b | (StB,S1) => instruction_bitB1 b
 | (StC,S0) => instruction_bitC0 b | (StC,S1) => instruction_bitC1 b
 | (StD,S0) => instruction_bitD0 b | (StD,S1) => instruction_bitD1 b end.
Definition instruction_bit_mark q b := InstructionBits
 (instruction_bitA0 b || instr_eqb q (StA,S0))
 (instruction_bitA1 b || instr_eqb q (StA,S1))
 (instruction_bitB0 b || instr_eqb q (StB,S0))
 (instruction_bitB1 b || instr_eqb q (StB,S1))
 (instruction_bitC0 b || instr_eqb q (StC,S0))
 (instruction_bitC1 b || instr_eqb q (StC,S1))
 (instruction_bitD0 b || instr_eqb q (StD,S0))
 (instruction_bitD1 b || instr_eqb q (StD,S1)).
Lemma instruction_bit_get_mark : forall q s b,
 instruction_bit_get q (instruction_bit_mark s b) = instruction_bit_get q b || instr_eqb s q.
Proof. intros [q h] s b; destruct q,h; reflexivity. Qed.
Definition instruction_observation_body tm (s:option cconf * instruction_bits) :=
 match s with (Some c,b) => (cstep tm c,instruction_bit_mark (cinstr_of c) b) | (None,b)=>(None,b) end.
Definition instruction_observation_scan tm w c := N.iter w (instruction_observation_body tm) (Some c,no_instruction_bits).
Definition instruction_observation_window tm B w :=
 match cstepsN tm B c0 with
 | None => (None,no_instruction_bits)
 | Some c => let '(oc,b):=instruction_observation_scan tm w c in
   (oc,match oc with Some e=>instruction_bit_mark (cinstr_of e) b|None=>b end)
 end.

Lemma instruction_observation_fst : forall tm n oc b,
 fst (Nat.iter n (instruction_observation_body tm) (oc,b)) =
 match oc with Some c=>csteps tm n c|None=>None end.
Proof.
 intros tm n; induction n; intros oc b; [destruct oc; reflexivity|].
 rewrite Nat.iter_succ_r; destruct oc as [c|]; cbn [instruction_observation_body]; rewrite IHn.
 - simpl; destruct (cstep tm c); reflexivity.
 - reflexivity.
Qed.
Lemma instruction_observation_snd : forall tm n oc b q,
 instruction_bit_get q (snd (Nat.iter n (instruction_observation_body tm) (oc,b))) = instruction_bit_get q b ||
 match oc with Some c=>visits tm (fun c=>instr_eqb (cinstr_of c) q) n c|None=>false end.
Proof.
 intros tm n; induction n; intros oc b q.
 - destruct oc; simpl; now rewrite orb_false_r.
 - rewrite Nat.iter_succ_r; destruct oc as [c|]; cbn [instruction_observation_body]; rewrite IHn.
   + rewrite instruction_bit_get_mark; cbn [visits]; destruct (cstep tm c); rewrite ?orb_assoc; reflexivity.
   + now rewrite orb_false_r.
Qed.
Theorem instruction_observation_window_witness : forall tm B w oc bits,
 instruction_observation_window tm B w=(oc,bits) -> forall q, instruction_bit_get q bits=true ->
 exists i d, i<=N.to_nat w /\ csteps tm (N.to_nat B+i) c0=Some d /\ cinstr_of d=q.
Proof.
 intros tm B w oc bits HW q HQ; unfold instruction_observation_window in HW; rewrite cstepsN_nat in HW.
 destruct (csteps tm (N.to_nat B) c0) as [c|] eqn:HB.
 - destruct (instruction_observation_scan tm w c) as [oe b] eqn:HS; injection HW as <- <-.
   pose proof (instruction_observation_snd tm (N.to_nat w) (Some c) no_instruction_bits q) as HV.
   pose proof (instruction_observation_fst tm (N.to_nat w) (Some c) no_instruction_bits) as HF.
   rewrite <- N2Nat.inj_iter in HV,HF; fold (instruction_observation_scan tm w c) in HV,HF.
   rewrite HS in HV,HF; cbn [fst snd] in HV,HF.
   assert (HZ : instruction_bit_get q no_instruction_bits=false) by (destruct q as [q h]; destruct q,h; reflexivity).
   rewrite HZ in HV; cbn [orb] in HV.
   assert (Hprefix : instruction_bit_get q b=true -> exists i d, i<=N.to_nat w /\
     csteps tm (N.to_nat B+i) c0=Some d /\ cinstr_of d=q).
   { intro HP; rewrite HP in HV; symmetry in HV.
     destruct (visits_sound tm _ _ c HV) as (i & d & Hi & HR & HH).
     apply instr_eqb_spec in HH; exists i,d; split; [lia|]; split; [rewrite csteps_add,HB; exact HR|exact HH]. }
   destruct oe as [e|].
   + rewrite instruction_bit_get_mark in HQ; apply orb_true_iff in HQ as [HQ|HQ]; [apply Hprefix; exact HQ|].
     apply instr_eqb_spec in HQ; exists (N.to_nat w),e; split; [lia|].
     split; [rewrite csteps_add,HB; symmetry; exact HF|exact HQ].
   + apply Hprefix; exact HQ.
 - injection HW as <- <-; destruct q as [q h]; destruct q,h; discriminate HQ.
Qed.

Lemma instruction_observation_window_endpoint : forall tm B w e bits,
 instruction_observation_window tm B w=(Some e,bits) ->
 csteps tm (N.to_nat B+N.to_nat w) c0=Some e.
Proof.
 intros tm B w e bits HW; unfold instruction_observation_window in HW; rewrite cstepsN_nat in HW.
 destruct (csteps tm (N.to_nat B) c0) as [c|] eqn:HB; [|discriminate].
 destruct (instruction_observation_scan tm w c) as [oe b] eqn:HS; injection HW as <- Heq.
 pose proof (instruction_observation_fst tm (N.to_nat w) (Some c) no_instruction_bits) as HF.
 rewrite <- N2Nat.inj_iter in HF; fold (instruction_observation_scan tm w c) in HF.
 rewrite HS in HF; cbn [fst] in HF; rewrite csteps_add,HB; symmetry; exact HF.
Qed.

Lemma instruction_observation_completion_beep : forall tm tm' B w oc bits q,
 TM_le tm tm' -> instruction_observation_window tm B w=(oc,bits) -> instruction_bit_get q bits=true ->
 BeepWindowTr tm' q (N.to_nat B) (N.to_nat w).
Proof.
 intros tm tm' B w oc bits q Hle HW HQ.
 destruct (instruction_observation_window_witness tm B w oc bits HW q HQ) as (i & d & Hi & HR & Hq).
 exists (N.to_nat B+i); repeat split; try lia.
 exists (lift d); split.
 - eapply TM_le_stepn; [exact Hle|rewrite <- lift_c0; apply csteps_lift; exact HR].
 - rewrite cinstr_of_lift; exact Hq.
Qed.

Definition all_instruction_bits bits := forallb (fun q=>instruction_bit_get q bits) all_Instr.
Definition instruction_tail_observed tm inv bits (endpoint : cconf) :=
 inv (fst endpoint) && cr_closed_ok tm inv &&
 forallb (fun q=>if inv (fst q) then instruction_bit_get q bits else true) all_Instr.
Definition finite_instruction_observation_check tm inv B w :=
 let '(oc,bits):=instruction_observation_window tm B w in
 all_instruction_bits bits || match oc with Some e=>instruction_tail_observed tm inv bits e|None=>false end.

Theorem finite_instruction_observation_check_completion : forall tm inv B w,
 finite_instruction_observation_check tm inv B w=true -> forall tm', TM_le tm tm' ->
 WindowBoundTr tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv B w HC tm' Hle q HF.
 unfold finite_instruction_observation_check in HC; destruct (instruction_observation_window tm B w) as [oc bits] eqn:HW.
 apply orb_true_iff in HC as [HA|HT].
 - unfold all_instruction_bits in HA; rewrite forallb_forall in HA.
   eapply instruction_observation_completion_beep; [exact Hle|exact HW|apply HA; apply all_Instr_complete].
 - destruct oc as [e|]; [|discriminate]; unfold instruction_tail_observed in HT.
   repeat rewrite andb_true_iff in HT; destruct HT as [[HI HC] HO].
   destruct HF as (t & Ht & cq & HR & Hq).
   destruct (le_dec t (N.to_nat B+N.to_nat w)) as [Hearly|Hlate].
   + exists t; repeat split; auto; exists cq; auto.
   + pose proof (instruction_observation_window_endpoint tm B w e bits HW) as HE.
     assert (HE' : stepn tm' (N.to_nat B+N.to_nat w) InitES=Some (lift e)).
     { eapply TM_le_stepn; [exact Hle|rewrite <- lift_c0; apply csteps_lift; exact HE]. }
     replace t with ((N.to_nat B+N.to_nat w)+(t-(N.to_nat B+N.to_nat w))) in HR by lia.
     rewrite stepn_add,HE' in HR.
     assert (HI' : inv (fst (lift e))=true) by (destruct e as [s [[l h] r]]; exact HI).
     pose proof (observation_tail_closed tm tm' inv Hle HC _ _ _ HI' HR) as HQ.
     assert (Hstate : fst cq = fst q) by (change (fst (instr_of cq) = fst q); now rewrite Hq).
     rewrite Hstate in HQ; rewrite forallb_forall in HO; specialize (HO q (all_Instr_complete q)); rewrite HQ in HO.
     eapply instruction_observation_completion_beep; eauto.
Qed.
Print Assumptions finite_instruction_observation_check_completion.

(** Every entry has its own checked finite window. The binary gate checks
    that this local width fits the requested common width before widening. *)
Record instruction_observation_case := mkInstructionObservationCase {
 instruction_observation_machine : TM;
 instruction_observation_inv : St -> bool;
 instruction_observation_width : N
}.
Definition instruction_observation_batch_check (entries : list instruction_observation_case) (B W : N) :=
 forallb (fun e => N.leb (instruction_observation_width e) W &&
   finite_instruction_observation_check (instruction_observation_machine e) (instruction_observation_inv e) B
     (instruction_observation_width e)) entries.

Theorem instruction_observation_batch_completion : forall entries B W,
 instruction_observation_batch_check entries B W = true ->
 forall e, In e entries -> forall tm', TM_le (instruction_observation_machine e) tm' ->
 WindowBoundTr tm' (N.to_nat B) (N.to_nat W).
Proof.
 intros entries B W HC e HI tm' Hle.
 unfold instruction_observation_batch_check in HC; rewrite forallb_forall in HC.
 specialize (HC e HI); apply andb_true_iff in HC as [HW HC].
 apply N.leb_le in HW.
 eapply windowTr_mono.
 - assert (Hnat : N.to_nat (instruction_observation_width e) <= N.to_nat W) by lia.
   exact Hnat.
 - exact (finite_instruction_observation_check_completion (instruction_observation_machine e)
     (instruction_observation_inv e) B (instruction_observation_width e) HC tm' Hle).
Qed.

Print Assumptions instruction_observation_batch_completion.
