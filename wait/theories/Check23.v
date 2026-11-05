(** Replayed finite certificates for two-state, three-symbol waiting. *)
From Coq Require Import List Bool Lia.
From SmallBB Require Import Statement.
From BBBWait Require Import Spec SpecTr Fast Tail HistoricalWait Exceptional23
  Monotone Check32 Census23.
Import ListNotations.

Definition state23_profiles : list (bool * nat * nat) := [(false,1,0);
    (true,1,0);
    (false,2,0);
    (false,2,1);
    (false,3,1);
    (true,3,1);
    (false,3,0);
    (true,3,0)].
Definition instr23_profiles : list (bool * nat * nat) := [(false,1,0);
    (true,1,0);
    (false,2,0);
    (true,2,0);
    (false,4,0);
    (false,3,0);
    (true,3,0);
    (true,4,0);
    (false,2,1);
    (false,3,1);
    (true,3,1);
    (false,4,1);
    (true,4,1);
    (false,5,0);
    (true,5,0);
    (false,6,0);
    (true,6,0);
    (false,5,1);
    (true,5,1);
    (false,7,1);
    (true,7,1);
    (false,6,1);
    (false,8,1);
    (true,8,1);
    (true,6,1);
    (false,7,0);
    (true,7,0);
    (false,6,2);
    (true,6,2);
    (false,5,2);
    (true,5,2);
    (false,8,0);
    (true,8,0);
    (false,9,0);
    (true,9,0);
    (false,9,2);
    (true,9,2);
    (false,9,1);
    (true,9,1);
    (false,8,2);
    (false,10,1);
    (true,10,1);
    (true,8,2);
    (false,10,0);
    (true,10,0);
    (false,12,0);
    (false,7,2);
    (true,7,2);
    (false,11,0);
    (true,11,0);
    (false,12,2);
    (true,12,2);
    (false,12,1);
    (true,12,0);
    (false,11,1);
    (true,11,1);
    (false,8,3);
    (true,8,3);
    (false,4,2);
    (false,13,2);
    (true,13,2);
    (false,10,2);
    (true,10,2);
    (false,11,2);
    (true,11,2);
    (true,12,1);
    (false,12,3);
    (true,12,3);
    (false,13,0);
    (true,13,0);
    (false,14,2);
    (true,14,2);
    (false,14,0);
    (true,14,0);
    (false,14,1);
    (true,14,1);
    (false,10,3);
    (true,10,3);
    (false,18,1);
    (true,18,1);
    (false,13,1);
    (true,13,1);
    (false,9,3);
    (true,9,3);
    (false,14,3);
    (true,14,3);
    (false,11,3);
    (true,11,3);
    (false,15,0);
    (true,15,0);
    (false,15,2);
    (true,15,2);
    (false,16,1);
    (true,16,1);
    (false,16,2);
    (true,16,2);
    (false,54,0);
    (true,54,0);
    (false,7,3);
    (true,7,3);
    (false,19,1);
    (true,19,1);
    (false,18,0);
    (true,18,0);
    (false,13,4);
    (true,13,4);
    (false,6,3);
    (false,16,0);
    (true,16,0);
    (false,19,0);
    (true,19,0);
    (false,12,4);
    (true,12,4);
    (false,13,3);
    (true,13,3);
    (false,15,3);
    (true,15,3);
    (false,18,2);
    (true,18,2);
    (false,20,3);
    (true,20,3);
    (false,20,4);
    (true,20,4);
    (false,21,3);
    (true,21,3);
    (false,23,3);
    (true,23,3)].

Definition state23_check tm :=
  if fast_drift_check tm 59 then true else
  if fast_static_state_check tm 59 32 then true else
  find_success (fun p => let '(mirror,period,width) := p in
    fast_tc_wait_check_state tm 59 32 mirror 91 period width) state23_profiles.
Lemma state23_check_sound : forall tm, state23_check tm = true ->
  forall q, FutureBeep tm q 59 -> BeepWindow tm q 59 32.
Proof.
  intros tm H; unfold state23_check in H.
  destruct (fast_drift_check tm 59) eqn:Ed.
  { exact (fast_drift_check_state_sound tm 59 Ed 32). }
  destruct (fast_static_state_check tm 59 32) eqn:E.
  - now apply fast_static_state_check_sound.
  - apply find_success_sound in H as ([[m p] w] & H).
    exact (fast_tc_wait_check_state_sound tm 59 32 m 91 p w H).
Qed.

Definition instr23_stage tm w :=
  if fast_static_instr_check_full tm 67 w then true else
  find_success (fun p => let '(mirror,period,width) := p in
    fast_tc_wait_check_tr tm 67 w mirror (67+w) period width) instr23_profiles.
Lemma instr23_stage_sound : forall tm w, instr23_stage tm w = true ->
  forall tg, FutureBeepTr tm tg 67 -> BeepWindowTr tm tg 67 w.
Proof.
  intros tm w H; unfold instr23_stage in H.
  destruct (fast_static_instr_check_full tm 67 w) eqn:E.
  - now apply fast_static_instr_check_full_sound.
  - apply find_success_sound in H as ([[m p] width] & H).
    exact (fast_tc_wait_check_tr_sound tm 67 w m (67+w) p width H).
Qed.

(** Almost all tables finish in the short window. The monotonicity lemma
    transfers those certificates to the exact global window. *)
Definition instr23_check tm :=
  if fast_drift_check tm 67 then true else
  if instr23_stage tm 32 then true else
  if instr23_stage tm 693 then true else
  if hn_wait_check_tr tm 67 693 2 2 760 2048 32 then true else
  rw_wait_check_tr tm 67 693 2 2 760 4096.
Lemma instr23_check_sound : forall tm, instr23_check tm = true ->
  forall tg, FutureBeepTr tm tg 67 -> BeepWindowTr tm tg 67 693.
Proof.
  intros tm H; unfold instr23_check in H.
  destruct (fast_drift_check tm 67) eqn:Ed.
  { exact (fast_drift_check_sound tm 67 Ed 693). }
  destruct (instr23_stage tm 32) eqn:Eshort.
  { apply (instr_wait_monotone tm 67 32 693); [lia|].
    now apply instr23_stage_sound. }
  destruct (instr23_stage tm 693) eqn:Elong.
  { now apply instr23_stage_sound. }
  destruct (hn_wait_check_tr tm 67 693 2 2 760 2048 32) eqn:Eh.
  { exact (hn_wait_check_tr_sound tm 67 693 2 2 760 2048 32 Eh). }
  exact (rw_wait_check_tr_sound tm 67 693 2 2 760 4096 H).
Qed.
