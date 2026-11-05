(** Keep the checked small windows while discharging residuals at a larger
    proposed champion width. The stored frontier and its computation are reused. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBB4_Spec.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Census Run Resume ReplayPilot.
Import ListNotations.
Local Opaque champion_score pilot_walk replay_pilot_checker.

Theorem replay_pilot_checker_sound_at_width : forall w,
 4096 <= w -> waiting_checker_sound champion_score w replay_pilot_checker.
Proof.
 intros w Hw tm HC.
 destruct (replay_pilot_checker_sound tm HC) as [HN HB].
 split; [exact HN|]. eapply window_mono; [exact Hw|exact HB].
Qed.

Theorem replay_pilot_coverage_at_width : forall w,
 4096 <= w ->
 (forall x, In x replay_pilot_residual ->
   Census.NodeDecided champion_score w [] (node_tm x)) ->
 WaitBound champion_score w.
Proof.
 intros w Hw Hres.
 apply (pilot_resume_wait_bound w 10 replay_pilot_checker).
 - exact Hw.
 - apply replay_pilot_checker_sound_at_width; exact Hw.
 - exact Hres.
Qed.

Print Assumptions replay_pilot_coverage_at_width.
