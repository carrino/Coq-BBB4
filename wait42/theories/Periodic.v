(** Binary anchor certificates for translated cycles. Only the anchor and one
    guarded lap are evaluated; the later cutoff is a proof parameter. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import TCycler TCyclerN.
From BBBWait42 Require Import Spec Transport.
Import ListNotations.

Definition periodic_check (tm : TM) (anchor : N) (P W : nat) : bool :=
  (0 <? P) &&
  match cstepsN tm anchor c0 with
  | Some (q, (l,h,r)) =>
      let g := (q, (firstn_pad W l,h,r)) in
      match gsteps tm P g with
      | Some g' => gmatch g g'
      | None => false
      end
  | None => false
  end.

Lemma lap_in_window : forall a P B i,
  0 < P -> a <= B -> i < P ->
  exists k, B <= a + k*P+i /\ a+k*P+i <= B+(P-1).
Proof.
 intros a P B i HP Ha Hi.
 pose proof (Nat.div_mod_eq (B-a) P) as HD.
 pose proof (Nat.mod_upper_bound (B-a) P ltac:(lia)) as HR.
 destruct (le_dec ((B-a) mod P) i) as [Hle|Hgt].
 - exists ((B-a)/P); split; nia.
 - exists (S ((B-a)/P)); split; nia.
Qed.

Lemma translated_cycle_replay : forall tm a P g g' rho0,
  0 < P -> stepn tm a InitES = Some (glift rho0 g) ->
  gsteps tm P g = Some g' -> gmatch g g' = true ->
  forall B n c, a <= B -> B <= n -> stepn tm n InitES = Some c ->
  exists t gi rho rho', B <= t /\ t <= B+(P-1) /\
    c = glift rho gi /\ stepn tm t InitES = Some (glift rho' gi).
Proof.
 intros tm a P g g' rho0 HP HA HG HM B n c Ha Hn HC.
 destruct (tcycler_fold tm a P g g' rho0 HP HA HG HM n ltac:(lia))
   as (i&gi&rho&Hi&HI&HF).
 rewrite HF in HC; injection HC as <-.
 destruct (lap_in_window a P B i HP Ha Hi) as (k&HL&HU).
 destruct (tcycler_laps tm a P g g' rho0 HA HG HM k) as (rho'&HK).
 exists (a+k*P+i), gi, rho, rho'; repeat split; auto.
 rewrite stepn_add, HK; apply gsteps_lift; exact HI.
Qed.

Lemma translated_cycle_window : forall tm a P g g' rho0,
  0 < P -> stepn tm a InitES = Some (glift rho0 g) ->
  gsteps tm P g = Some g' -> gmatch g g' = true ->
  forall B, a <= B -> WindowBound tm B (P-1) /\ WindowBoundTr tm B (P-1).
Proof.
 intros tm a P g g' rho0 HP HA HG HM B HB; split.
 - intros q (n&Hn&c&HC&Hq).
   destruct (translated_cycle_replay tm a P g g' rho0 HP HA HG HM B n c HB Hn HC)
     as (t&gi&rho&rho'&HL&HU&->&HT).
   exists t; repeat split; auto.
   exists (glift rho' gi); split; [exact HT|].
   destruct gi as [qi [[li hi] ri]]; exact Hq.
 - intros q (n&Hn&c&HC&Hq).
   destruct (translated_cycle_replay tm a P g g' rho0 HP HA HG HM B n c HB Hn HC)
     as (t&gi&rho&rho'&HL&HU&->&HT).
   exists t; repeat split; auto.
   exists (glift rho' gi); split; [exact HT|].
   destruct gi as [qi [[li hi] ri]]; exact Hq.
Qed.

Theorem periodic_check_sound : forall tm anchor P W,
 periodic_check tm anchor P W = true ->
 forall B, N.to_nat anchor <= B ->
 WindowBound tm B (P-1) /\ WindowBoundTr tm B (P-1).
Proof.
 intros tm anchor P W H B HB.
 unfold periodic_check in H; apply andb_prop in H as [HP H].
 apply Nat.ltb_lt in HP; rewrite cstepsN_nat in H.
 destruct (csteps tm (N.to_nat anchor) c0) as [[q [[l h] r]]|] eqn:HA;
   [|discriminate].
 destruct (gsteps tm P (q,(firstn_pad W l,h,r))) as [g'|] eqn:HG;
   [|discriminate].
 eapply translated_cycle_window; eauto using anchor_instance.
Qed.

Corollary periodic_check_state_sound : forall tm anchor P W,
 periodic_check tm anchor P W = true ->
 forall B, N.to_nat anchor <= B -> WindowBound tm B (P-1).
Proof. intros; exact (proj1 (periodic_check_sound tm anchor P W H B H0)). Qed.
Corollary periodic_check_instruction_sound : forall tm anchor P W,
 periodic_check tm anchor P W = true ->
 forall B, N.to_nat anchor <= B -> WindowBoundTr tm B (P-1).
Proof. intros; exact (proj2 (periodic_check_sound tm anchor P W H B H0)). Qed.

Corollary periodic_check_sound_L : forall tm anchor P W,
 periodic_check (mirror_tm tm) anchor P W = true ->
 forall B, N.to_nat anchor <= B ->
 WindowBound tm B (P-1) /\ WindowBoundTr tm B (P-1).
Proof.
 intros tm anchor P W H B HB.
 destruct (periodic_check_sound (mirror_tm tm) anchor P W H B HB) as [HS HT].
 split; [apply (proj1 (window_bound_mirror tm B (P-1)))|
 apply (proj1 (window_boundTr_mirror tm B (P-1)))]; assumption.
Qed.

(** Small executable regressions: a two-state translated cycle. *)
Definition periodic_example_R : TM := fun q _ =>
 Some (mkTrans S0 DR (match q with StA => StB | _ => StA end)).
Definition periodic_example_L : TM := fun q _ =>
 Some (mkTrans S0 DL (match q with StA => StB | _ => StA end)).

Example periodic_right_accepts : periodic_check periodic_example_R 3%N 2 0 = true.
Proof. vm_compute; reflexivity. Qed.
Example periodic_left_accepts :
 periodic_check (mirror_tm periodic_example_L) 3%N 2 0 = true.
Proof. vm_compute; reflexivity. Qed.
Example periodic_rejects_zero : periodic_check periodic_example_R 0%N 0 0 = false.
Proof. vm_compute; reflexivity. Qed.
Example periodic_rejects_bad_period : periodic_check periodic_example_R 0%N 1 0 = false.
Proof. vm_compute; reflexivity. Qed.

(** At cutoff 1, A next occurs exactly at the inclusive endpoint 2.
    This also exercises the next-lap branch in [lap_in_window]. *)
Example periodic_boundary_window : BeepWindow periodic_example_R StA 1 1.
Proof.
 exists 2; repeat split; try lia.
 eexists; split; [vm_compute; reflexivity|reflexivity].
Qed.
Example periodic_boundary_not_zero : ~ BeepWindow periodic_example_R StA 1 0.
Proof.
 intros (t&HL&HU&c&HC&Hq).
 assert (t=1) by lia; subst t.
 vm_compute in HC; injection HC as <-; discriminate.
Qed.
Example periodic_boundary_instruction :
 BeepWindowTr periodic_example_R (StA,S0) 1 1.
Proof.
 exists 2; repeat split; try lia.
 eexists; split; [vm_compute; reflexivity|reflexivity].
Qed.
Example periodic_boundary_bound :
 WindowBound periodic_example_R 1 1 /\ WindowBoundTr periodic_example_R 1 1.
Proof.
 exact (periodic_check_sound periodic_example_R 0%N 2 0 eq_refl 1 ltac:(simpl; lia)).
Qed.

Print Assumptions periodic_check_sound.
Print Assumptions periodic_check_sound_L.

Theorem periodic_check_nonhalt : forall tm anchor P W,
 periodic_check tm anchor P W = true -> NonHalt tm.
Proof.
 intros tm anchor P W H n Hnone.
 unfold periodic_check in H; apply andb_prop in H as [HP H].
 apply Nat.ltb_lt in HP; rewrite cstepsN_nat in H.
 destruct (csteps tm (N.to_nat anchor) c0) as [[q [[l h] r]]|] eqn:HA;
   [|discriminate].
 destruct (gsteps tm P (q,(firstn_pad W l,h,r))) as [g'|] eqn:HG;
   [|discriminate].
 pose proof (anchor_instance tm (N.to_nat anchor) W q l h r HA) as Hanchor.
 destruct (tcycler_fold tm (N.to_nat anchor) P _ _ _ HP Hanchor HG H
   (N.to_nat anchor+n) ltac:(lia)) as (i&gi&rho&_&_&HF).
 replace (N.to_nat anchor+n) with (n+N.to_nat anchor) in HF by lia.
 rewrite stepn_add, Hnone in HF; discriminate.
Qed.
