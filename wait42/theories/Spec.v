(** Inclusive windows of configuration indices, on the full (4,2) carrier. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec BBBT4_Spec.

Definition FutureBeep tm q B := exists t, B <= t /\ VisitsAt tm q t.
Definition BeepWindow tm q B w := exists t, B <= t /\ t <= B+w /\ VisitsAt tm q t.
Definition WindowBound tm B w := forall q,
 FutureBeep tm q B -> BeepWindow tm q B w.
Definition WaitBound B w := forall tm, WindowBound tm B w.
Definition BBBWait42_is w := BBB4_is champion_score /\
 WaitBound champion_score w /\ forall v, WaitBound champion_score v -> w <= v.
Definition BBBQHDecide42_is D := exists w, BBBWait42_is w /\ D = champion_score+w.

Theorem wait_decides_future : forall B w, WaitBound B w -> forall tm q,
 FutureBeep tm q B <-> BeepWindow tm q B w.
Proof. intros B w H tm q; split; [apply H|]. intros (t&Ht&_&Hv); exists t; auto. Qed.
Theorem wait_silence_decision : forall B w, WaitBound B w -> forall tm q,
 (forall t,B<=t->t<=B+w->~VisitsAt tm q t) <-> QuietFrom tm q B.
Proof.
 intros B w H tm q; split.
 - intros Hnone t Ht Hv; destruct (H tm q (ex_intro _ t (conj Ht Hv))) as (k&Hk&Hkw&Hvk).
   exact (Hnone k Hk Hkw Hvk).
 - intros Hnone t Ht _; exact (Hnone t Ht).
Qed.
Theorem window_mono : forall tm B w v, w <= v ->
 WindowBound tm B w -> WindowBound tm B v.
Proof. intros tm B w v Hle H q Hf; destruct (H q Hf) as (t&Ht&Hu&Hv).
 exists t; repeat split; auto; lia. Qed.
Theorem wait_mono : forall B w v, w<=v -> WaitBound B w -> WaitBound B v.
Proof. intros B w v Hle H tm; eapply window_mono; eauto. Qed.
Theorem BBBWait42_is_unique : forall w v, BBBWait42_is w -> BBBWait42_is v -> w=v.
Proof. intros w v [_ [Hw Hmw]] [_ [Hv Hmv]]; specialize (Hmw v Hv); specialize (Hmv w Hw); lia. Qed.
Theorem BBBQHDecide42_unique : forall D E,
 BBBQHDecide42_is D -> BBBQHDecide42_is E -> D=E.
Proof. intros D E (w&Hw&->) (v&Hv&->); rewrite (BBBWait42_is_unique w v Hw Hv); reflexivity. Qed.

Definition FutureBeepTr tm q B := exists t, B <= t /\ FiresAt tm q t.
Definition BeepWindowTr tm q B w := exists t, B <= t /\ t <= B+w /\ FiresAt tm q t.
Definition WindowBoundTr tm B w := forall q,
 FutureBeepTr tm q B -> BeepWindowTr tm q B w.
Definition WaitBoundTr B w := forall tm, WindowBoundTr tm B w.
Definition BBBWaitTr42_is w := BBBT4_is champion_score /\
 WaitBoundTr champion_score w /\ forall v, WaitBoundTr champion_score v -> w <= v.
Definition BBBQHDecideTr42_is D := exists w, BBBWaitTr42_is w /\ D = champion_score+w.

Theorem waitTr_decides_future : forall B w, WaitBoundTr B w -> forall tm q,
 FutureBeepTr tm q B <-> BeepWindowTr tm q B w.
Proof. intros B w H tm q; split; [apply H|]. intros (t&Ht&_&Hv); exists t; auto. Qed.
Theorem waitTr_silence_decision : forall B w, WaitBoundTr B w -> forall tm q,
 (forall t,B<=t->t<=B+w->~FiresAt tm q t) <-> QuietFromTr tm q B.
Proof.
 intros B w H tm q; split.
 - intros Hnone t Ht Hv; destruct (H tm q (ex_intro _ t (conj Ht Hv))) as (k&Hk&Hkw&Hvk).
   exact (Hnone k Hk Hkw Hvk).
 - intros Hnone t Ht _; exact (Hnone t Ht).
Qed.
Theorem windowTr_mono : forall tm B w v, w <= v ->
 WindowBoundTr tm B w -> WindowBoundTr tm B v.
Proof. intros tm B w v Hle H q Hf; destruct (H q Hf) as (t&Ht&Hu&Hv).
 exists t; repeat split; auto; lia. Qed.
Theorem waitTr_mono : forall B w v, w<=v -> WaitBoundTr B w -> WaitBoundTr B v.
Proof. intros B w v Hle H tm; eapply windowTr_mono; eauto. Qed.
Theorem BBBWaitTr42_is_unique : forall w v, BBBWaitTr42_is w -> BBBWaitTr42_is v -> w=v.
Proof. intros w v [_ [Hw Hmw]] [_ [Hv Hmv]]; specialize (Hmw v Hv); specialize (Hmv w Hw); lia. Qed.
Theorem BBBQHDecideTr42_unique : forall D E,
 BBBQHDecideTr42_is D -> BBBQHDecideTr42_is E -> D=E.
Proof. intros D E (w&Hw&->) (v&Hv&->); rewrite (BBBWaitTr42_is_unique w v Hw Hv); reflexivity. Qed.

Theorem instruction_window_implies_state : forall tm B w,
 WindowBoundTr tm B w -> WindowBound tm B w.
Proof.
 intros tm B w H q (t&Ht&Hv).
 apply visits_fires in Hv; destruct Hv as (a&Hf).
 destruct (H (q,a) (ex_intro _ t (conj Ht Hf))) as (u&Hu&Hub&Hfu).
 exists u; repeat split; auto; eapply fires_visits; eauto.
Qed.
Theorem instruction_upper_implies_state_upper : forall B w,
 WaitBoundTr B w -> WaitBound B w.
Proof. intros B w H tm; apply instruction_window_implies_state, H. Qed.
