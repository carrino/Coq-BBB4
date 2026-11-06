(** Small periodic certificates, with binary bounds and completion transport.
    Machine decoding is deliberately a caller responsibility: entries accept
    ordinary [TM] values, including partially specified transition tables. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport Periodic.
Import ListNotations.

Record periodic_certificate := {
  pc_anchor : N;
  pc_period : nat;
  pc_width : nat;
  pc_left : bool
}.

Definition periodic_certificate_check tm c :=
  periodic_check (if pc_left c then mirror_tm tm else tm)
    (pc_anchor c) (pc_period c) (pc_width c).

(** Neither the cutoff nor the requested window is expanded to unary during
    checking. Only the small lap length is converted to binary. *)
Definition periodic_bounds_check (B w : N) c :=
  N.leb (pc_anchor c) B && N.leb (N.of_nat (pc_period c - 1)) w.

Definition periodic_entry_check (B w : N) (e : TM * periodic_certificate) :=
  periodic_bounds_check B w (snd e) && periodic_certificate_check (fst e) (snd e).
Definition periodic_batch_check (B w : N) (entries : list (TM * periodic_certificate)) :=
  forallb (periodic_entry_check B w) entries.

Definition periodic_result tm B w :=
  NonHalt tm /\ WindowBound tm B w /\ WindowBoundTr tm B w.

Theorem periodic_certificate_sound : forall tm c,
  periodic_certificate_check tm c = true ->
  forall B, N.to_nat (pc_anchor c) <= B ->
  periodic_result tm B (pc_period c - 1).
Proof.
 intros tm [a p W left] H B HB.
 unfold periodic_certificate_check in H; simpl in *.
 destruct left.
 - split.
   + apply mirror_nonhalt; eapply periodic_check_nonhalt; exact H.
   + exact (periodic_check_sound_L tm a p W H B HB).
 - split.
   + eapply periodic_check_nonhalt; exact H.
   + exact (periodic_check_sound tm a p W H B HB).
Qed.

Lemma periodic_bounds_check_sound : forall B w c,
  periodic_bounds_check B w c = true ->
  N.to_nat (pc_anchor c) <= N.to_nat B /\ pc_period c - 1 <= N.to_nat w.
Proof.
 intros B w c H; unfold periodic_bounds_check in H.
 apply andb_true_iff in H as [HB Hw].
 apply N.leb_le in HB; apply N.leb_le in Hw.
 split; lia.
Qed.

Theorem periodic_entry_sound : forall B w tm c,
 periodic_entry_check B w (tm,c) = true ->
 periodic_result tm (N.to_nat B) (N.to_nat w).
Proof.
 intros B w tm c H; unfold periodic_entry_check in H; simpl in H.
 apply andb_true_iff in H as [Hbounds Hcheck].
 destruct (periodic_bounds_check_sound B w c Hbounds) as [HB Hw].
 destruct (periodic_certificate_sound tm c Hcheck _ HB) as [HN [HS HT]].
 split; [exact HN|]; split.
 - eapply window_mono; eauto.
 - eapply windowTr_mono; eauto.
Qed.

(** Supply equalities to abstract natural bounds without evaluating large unary
    numerals in a generated certificate proof. *)
Corollary periodic_entry_sound_at : forall B w tm c Bnat wnat,
 periodic_entry_check B w (tm,c) = true ->
 N.to_nat B = Bnat -> N.to_nat w = wnat -> periodic_result tm Bnat wnat.
Proof. intros B w tm c Bnat wnat H <- <-; now apply periodic_entry_sound with c. Qed.

Theorem periodic_result_completion : forall tm tm' B w,
 periodic_result tm B w -> TM_le tm tm' -> periodic_result tm' B w.
Proof.
 intros tm tm' B w [HN [HS HT]] Hle; split.
 - eapply nonhalt_le; eauto.
 - split.
   + apply (proj2 (window_bound_completion tm tm' B w HN Hle)); exact HS.
   + apply (proj2 (window_boundTr_completion tm tm' B w HN Hle)); exact HT.
Qed.

Theorem periodic_batch_sound : forall B w entries,
 periodic_batch_check B w entries = true ->
 forall tm c, In (tm,c) entries -> periodic_result tm (N.to_nat B) (N.to_nat w).
Proof.
 intros B w entries H tm c Hin.
 unfold periodic_batch_check in H; rewrite forallb_forall in H.
 apply periodic_entry_sound with c; exact (H (tm,c) Hin).
Qed.

Corollary periodic_batch_completion : forall B w entries,
 periodic_batch_check B w entries = true ->
 forall tm c tm', In (tm,c) entries -> TM_le tm tm' ->
 periodic_result tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros B w entries H tm c tm' Hin Hle.
 eapply periodic_result_completion; [eapply periodic_batch_sound; eauto|exact Hle].
Qed.

Corollary periodic_batch_sound_at : forall B w entries Bnat wnat,
 periodic_batch_check B w entries = true ->
 N.to_nat B = Bnat -> N.to_nat w = wnat ->
 forall tm c, In (tm,c) entries -> periodic_result tm Bnat wnat.
Proof.
 intros B w entries Bnat wnat H <- <-.
 exact (periodic_batch_sound B w entries H).
Qed.

Corollary periodic_batch_completion_at : forall B w entries Bnat wnat,
 periodic_batch_check B w entries = true ->
 N.to_nat B = Bnat -> N.to_nat w = wnat ->
 forall tm c tm', In (tm,c) entries -> TM_le tm tm' -> periodic_result tm' Bnat wnat.
Proof.
 intros B w entries Bnat wnat H <- <-.
 exact (periodic_batch_completion B w entries H).
Qed.

Definition batch_example_right : periodic_certificate :=
 {| pc_anchor := 3%N; pc_period := 2; pc_width := 0; pc_left := false |}.
Definition batch_example_left : periodic_certificate :=
 {| pc_anchor := 3%N; pc_period := 2; pc_width := 0; pc_left := true |}.
Definition batch_example_bad_period : periodic_certificate :=
 {| pc_anchor := 3%N; pc_period := 1; pc_width := 0; pc_left := false |}.
Definition batch_example_zero_period : periodic_certificate :=
 {| pc_anchor := 3%N; pc_period := 0; pc_width := 0; pc_left := false |}.

Example batch_accepts_both_directions :
 periodic_batch_check 32779478%N 1%N
 [(periodic_example_R,batch_example_right); (periodic_example_L,batch_example_left)] = true.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_tampered_period :
 periodic_entry_check 32779478%N 1%N (periodic_example_R,batch_example_bad_period) = false.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_zero_period :
 periodic_entry_check 32779478%N 1%N (periodic_example_R,batch_example_zero_period) = false.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_early_cutoff :
 periodic_entry_check 2%N 1%N (periodic_example_R,batch_example_right) = false.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_short_window :
 periodic_entry_check 32779478%N 0%N (periodic_example_R,batch_example_right) = false.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_one_bad_entry :
 periodic_batch_check 32779478%N 1%N
 [(periodic_example_L,batch_example_left); (periodic_example_R,batch_example_bad_period)] = false.
Proof. vm_compute; reflexivity. Qed.

(** A partial table really exercises the completion theorem: six entries are
    unspecified, and may be filled arbitrarily without changing the trace. *)
Definition batch_example_partial : TM := fun q a =>
 match q,a with
 | StA,S0 => Some (mkTrans S0 DL StB)
 | StB,S0 => Some (mkTrans S0 DL StA)
 | _,_ => None
 end.
Example batch_partial_accepts :
 periodic_entry_check 3%N 1%N (batch_example_partial,batch_example_left) = true.
Proof. vm_compute; reflexivity. Qed.
Example batch_partial_all_completions : forall tm',
 TM_le batch_example_partial tm' -> periodic_result tm' 3 1.
Proof.
 intros tm' Hle; eapply periodic_result_completion; [|exact Hle].
 exact (periodic_entry_sound 3%N 1%N _ _ batch_partial_accepts).
Qed.

Print Assumptions periodic_batch_sound.
Print Assumptions periodic_batch_completion.
