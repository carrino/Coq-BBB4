(** Transport preserves absolute observation times. A prefix changes the cutoff. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBBWait42 Require Import Spec.

Lemma future_transport : forall tm tm' q q' B,
 (forall t, VisitsAt tm q t <-> VisitsAt tm' q' t) ->
 (FutureBeep tm q B <-> FutureBeep tm' q' B).
Proof. intros tm tm' q q' B H; unfold FutureBeep; split;
 intros (t&Ht&Hv); exists t; split; [exact Ht|apply H; exact Hv|exact Ht|apply H; exact Hv]. Qed.
Lemma window_transport : forall tm tm' q q' B w,
 (forall t, VisitsAt tm q t <-> VisitsAt tm' q' t) ->
 (BeepWindow tm q B w <-> BeepWindow tm' q' B w).
Proof. intros tm tm' q q' B w H; unfold BeepWindow; split;
 intros (t&Ht&Hu&Hv); exists t; repeat split; auto; apply H; exact Hv. Qed.
Theorem future_mirror : forall tm q B,
 FutureBeep (mirror_tm tm) q B <-> FutureBeep tm q B.
Proof. intros; apply future_transport; intro t; apply mirror_visits. Qed.
Theorem window_mirror : forall tm q B w,
 BeepWindow (mirror_tm tm) q B w <-> BeepWindow tm q B w.
Proof. intros; apply window_transport; intro t; apply mirror_visits. Qed.
Theorem window_bound_mirror : forall tm B w,
 WindowBound (mirror_tm tm) B w <-> WindowBound tm B w.
Proof. intros tm B w; split; intros H q Hf;
 [apply (proj1 (window_mirror tm q B w)); apply H; apply (proj2 (future_mirror tm q B)); exact Hf|
 apply (proj2 (window_mirror tm q B w)); apply H; apply (proj1 (future_mirror tm q B)); exact Hf]. Qed.
Theorem future_swap : forall u v tm q B,
 u <> StA -> v <> StA ->
 (FutureBeep (TM_swap u v tm) q B <-> FutureBeep tm (St_swap u v q) B).
Proof. intros; apply future_transport; intro t; apply visits_swap; assumption. Qed.
Theorem window_swap : forall u v tm q B w,
 u <> StA -> v <> StA ->
 (BeepWindow (TM_swap u v tm) q B w <-> BeepWindow tm (St_swap u v q) B w).
Proof. intros; apply window_transport; intro t; apply visits_swap; assumption. Qed.
Theorem window_bound_completion : forall tm tm' B w,
 NonHalt tm -> TM_le tm tm' ->
 (WindowBound tm' B w <-> WindowBound tm B w).
Proof.
 intros tm tm' B w Hnh Hle.
 assert (HF : forall q, FutureBeep tm' q B <-> FutureBeep tm q B).
 { intro q; apply future_transport; intro t; apply visits_le; assumption. }
 assert (HW : forall q, BeepWindow tm' q B w <-> BeepWindow tm q B w).
 { intro q; apply window_transport; intro t; apply visits_le; assumption. }
 split; intros H q Hf; [apply HW; apply H; apply HF; exact Hf|apply HW; apply H; apply HF; exact Hf].
Qed.
(** An explicit tail observation relation transports [B] to [k+B].
    The relation must be supplied: arbitrary prefixes do not preserve cutoffs. *)
Theorem future_shift : forall tm tm' q k B,
 (forall t, VisitsAt tm' q t <-> VisitsAt tm q (k+t)) ->
 (FutureBeep tm' q B <-> FutureBeep tm q (k+B)).
Proof.
 intros tm tm' q k B H; split.
 - intros (t&Ht&Hv); exists (k+t); split; [lia|apply H; exact Hv].
 - intros (t&Ht&Hv); exists (t-k); split; [lia|apply H; replace (k+(t-k)) with t by lia; exact Hv].
Qed.
Theorem window_shift : forall tm tm' q k B w,
 (forall t, VisitsAt tm' q t <-> VisitsAt tm q (k+t)) ->
 (BeepWindow tm' q B w <-> BeepWindow tm q (k+B) w).
Proof.
 intros tm tm' q k B w H; split.
 - intros (t&Ht&Hu&Hv); exists (k+t); repeat split; try lia; apply H; exact Hv.
 - intros (t&Ht&Hu&Hv); exists (t-k); repeat split; try lia; apply H;
   replace (k+(t-k)) with t by lia; exact Hv.
Qed.

Lemma futureTr_transport : forall tm tm' q q' B,
 (forall t, FiresAt tm q t <-> FiresAt tm' q' t) ->
 (FutureBeepTr tm q B <-> FutureBeepTr tm' q' B).
Proof. intros tm tm' q q' B H; unfold FutureBeepTr; split;
 intros (t&Ht&Hv); exists t; split; [exact Ht|apply H; exact Hv|exact Ht|apply H; exact Hv]. Qed.
Lemma windowTr_transport : forall tm tm' q q' B w,
 (forall t, FiresAt tm q t <-> FiresAt tm' q' t) ->
 (BeepWindowTr tm q B w <-> BeepWindowTr tm' q' B w).
Proof. intros tm tm' q q' B w H; unfold BeepWindowTr; split;
 intros (t&Ht&Hu&Hv); exists t; repeat split; auto; apply H; exact Hv. Qed.
Theorem futureTr_mirror : forall tm q B,
 FutureBeepTr (mirror_tm tm) q B <-> FutureBeepTr tm q B.
Proof. intros; apply futureTr_transport; intro t; apply mirror_fires. Qed.
Theorem windowTr_mirror : forall tm q B w,
 BeepWindowTr (mirror_tm tm) q B w <-> BeepWindowTr tm q B w.
Proof. intros; apply windowTr_transport; intro t; apply mirror_fires. Qed.
Theorem window_boundTr_mirror : forall tm B w,
 WindowBoundTr (mirror_tm tm) B w <-> WindowBoundTr tm B w.
Proof. intros tm B w; split; intros H q Hf;
 [apply (proj1 (windowTr_mirror tm q B w)); apply H; apply (proj2 (futureTr_mirror tm q B)); exact Hf|
 apply (proj2 (windowTr_mirror tm q B w)); apply H; apply (proj1 (futureTr_mirror tm q B)); exact Hf]. Qed.
Theorem futureTr_swap : forall u v tm q B,
 u <> StA -> v <> StA ->
 (FutureBeepTr (TM_swap u v tm) q B <-> FutureBeepTr tm (Instr_swap u v q) B).
Proof. intros; apply futureTr_transport; intro t; apply fires_swap; assumption. Qed.
Theorem windowTr_swap : forall u v tm q B w,
 u <> StA -> v <> StA ->
 (BeepWindowTr (TM_swap u v tm) q B w <-> BeepWindowTr tm (Instr_swap u v q) B w).
Proof. intros; apply windowTr_transport; intro t; apply fires_swap; assumption. Qed.
Theorem window_boundTr_completion : forall tm tm' B w,
 NonHalt tm -> TM_le tm tm' ->
 (WindowBoundTr tm' B w <-> WindowBoundTr tm B w).
Proof.
 intros tm tm' B w Hnh Hle.
 assert (HF : forall q, FutureBeepTr tm' q B <-> FutureBeepTr tm q B).
 { intro q; apply futureTr_transport; intro t; apply fires_le; assumption. }
 assert (HW : forall q, BeepWindowTr tm' q B w <-> BeepWindowTr tm q B w).
 { intro q; apply windowTr_transport; intro t; apply fires_le; assumption. }
 split; intros H q Hf; [apply HW; apply H; apply HF; exact Hf|apply HW; apply H; apply HF; exact Hf].
Qed.
(** An explicit tail observation relation transports [B] to [k+B].
    The relation must be supplied: arbitrary prefixes do not preserve cutoffs. *)
Theorem futureTr_shift : forall tm tm' q k B,
 (forall t, FiresAt tm' q t <-> FiresAt tm q (k+t)) ->
 (FutureBeepTr tm' q B <-> FutureBeepTr tm q (k+B)).
Proof.
 intros tm tm' q k B H; split.
 - intros (t&Ht&Hv); exists (k+t); split; [lia|apply H; exact Hv].
 - intros (t&Ht&Hv); exists (t-k); split; [lia|apply H; replace (k+(t-k)) with t by lia; exact Hv].
Qed.
Theorem windowTr_shift : forall tm tm' q k B w,
 (forall t, FiresAt tm' q t <-> FiresAt tm q (k+t)) ->
 (BeepWindowTr tm' q B w <-> BeepWindowTr tm q (k+B) w).
Proof.
 intros tm tm' q k B w H; split.
 - intros (t&Ht&Hu&Hv); exists (k+t); repeat split; try lia; apply H; exact Hv.
 - intros (t&Ht&Hu&Hv); exists (t-k); repeat split; try lia; apply H;
   replace (k+(t-k)) with t by lia; exact Hv.
Qed.

Theorem window_bound_swap : forall u v tm B w,
 u <> StA -> v <> StA ->
 (WindowBound (TM_swap u v tm) B w <-> WindowBound tm B w).
Proof.
 intros u v tm B w Hu Hv; split; intros H q Hf.
 - assert (HF : FutureBeep (TM_swap u v tm) (St_swap u v q) B).
   { apply (proj2 (future_swap u v tm (St_swap u v q) B Hu Hv)).
     rewrite St_swap_swap; exact Hf. }
   pose proof (proj1 (window_swap u v tm (St_swap u v q) B w Hu Hv) (H _ HF)) as HW.
   rewrite St_swap_swap in HW; exact HW.
 - apply (proj2 (window_swap u v tm q B w Hu Hv)); apply H.
   apply (proj1 (future_swap u v tm q B Hu Hv)); exact Hf.
Qed.
Theorem window_bound_shift : forall tm tm' k B w,
 (forall q t, VisitsAt tm' q t <-> VisitsAt tm q (k+t)) ->
 (WindowBound tm' B w <-> WindowBound tm (k+B) w).
Proof.
 intros tm tm' k B w H; split; intros HW q HF.
 - apply (proj1 (window_shift tm tm' q k B w (H q))); apply HW.
   apply (proj2 (future_shift tm tm' q k B (H q))); exact HF.
 - apply (proj2 (window_shift tm tm' q k B w (H q))); apply HW.
   apply (proj1 (future_shift tm tm' q k B (H q))); exact HF.
Qed.

Theorem window_boundTr_swap : forall u v tm B w,
 u <> StA -> v <> StA ->
 (WindowBoundTr (TM_swap u v tm) B w <-> WindowBoundTr tm B w).
Proof.
 intros u v tm B w Hu Hv; split; intros H q Hf.
 - assert (HF : FutureBeepTr (TM_swap u v tm) (Instr_swap u v q) B).
   { apply (proj2 (futureTr_swap u v tm (Instr_swap u v q) B Hu Hv)).
     rewrite Instr_swap_swap; exact Hf. }
   pose proof (proj1 (windowTr_swap u v tm (Instr_swap u v q) B w Hu Hv) (H _ HF)) as HW.
   rewrite Instr_swap_swap in HW; exact HW.
 - apply (proj2 (windowTr_swap u v tm q B w Hu Hv)); apply H.
   apply (proj1 (futureTr_swap u v tm q B Hu Hv)); exact Hf.
Qed.
Theorem window_boundTr_shift : forall tm tm' k B w,
 (forall q t, FiresAt tm' q t <-> FiresAt tm q (k+t)) ->
 (WindowBoundTr tm' B w <-> WindowBoundTr tm (k+B) w).
Proof.
 intros tm tm' k B w H; split; intros HW q HF.
 - apply (proj1 (windowTr_shift tm tm' q k B w (H q))); apply HW.
   apply (proj2 (futureTr_shift tm tm' q k B (H q))); exact HF.
 - apply (proj2 (windowTr_shift tm tm' q k B w (H q))); apply HW.
   apply (proj1 (futureTr_shift tm tm' q k B (H q))); exact HF.
Qed.
