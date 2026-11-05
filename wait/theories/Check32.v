(** Exhaustively replayed tail certificates for three-state binary waits. *)
From Coq Require Import List Bool.
From SmallBB Require Import Statement.
From BBBWait Require Import Spec SpecTr Static Tail HistoricalWait Census Fast.
Import ListNotations.

(** Explicit conditionals avoid eagerly evaluating unused certificates. *)
Fixpoint find_success {A : Type} (f : A -> bool) (xs : list A) :=
  match xs with [] => false | x::rest => if f x then true else find_success f rest end.
Lemma find_success_sound : forall A (f : A -> bool) xs,
  find_success f xs = true -> exists x, f x = true.
Proof.
  intros A f xs; induction xs as [|x xs IH]; intros H; [discriminate|].
  cbn [find_success] in H; destruct (f x) eqn:E.
  - exists x; exact E.
  - now apply IH.
Qed.

Definition state32_profiles : list (bool * nat * nat) :=
  [(true,1,0);
    (false,1,0);
    (false,2,0);
    (true,2,0);
    (false,2,1);
    (true,3,0);
    (false,3,0);
    (false,4,1);
    (false,4,0);
    (true,3,1);
    (false,3,1);
    (true,4,1);
    (true,4,0);
    (true,5,0);
    (false,5,0);
    (false,4,2);
    (true,5,1);
    (false,5,1);
    (false,5,2);
    (true,5,2)].
Definition instr32_profiles : list (bool * nat * nat) :=
  [(true,1,0);
    (false,1,0);
    (false,2,0);
    (true,2,0);
    (false,3,0);
    (true,3,0);
    (false,2,1);
    (false,4,0);
    (true,4,0);
    (true,3,1);
    (false,3,1);
    (false,4,1);
    (true,5,0);
    (false,5,0);
    (true,4,1);
    (true,5,1);
    (false,5,1);
    (false,6,0);
    (true,6,0);
    (false,6,1);
    (true,7,1);
    (false,7,1);
    (true,7,0);
    (false,7,0);
    (false,4,2);
    (true,6,1);
    (true,5,2);
    (false,5,2);
    (false,8,0);
    (true,8,0);
    (false,8,1);
    (true,8,1);
    (false,6,2);
    (false,10,0);
    (true,10,0);
    (false,7,2);
    (true,7,2);
    (true,9,0);
    (false,9,0);
    (false,8,2);
    (true,9,1);
    (false,9,1);
    (true,6,2);
    (true,8,2);
    (true,12,1);
    (false,12,1);
    (true,9,2);
    (false,9,2);
    (false,12,0);
    (true,12,0);
    (false,10,1);
    (true,10,1);
    (true,11,0);
    (false,10,2);
    (false,11,0);
    (true,10,2);
    (true,11,1);
    (false,11,1);
    (true,13,1);
    (false,13,1);
    (true,12,2);
    (false,12,2);
    (false,18,1);
    (true,18,1);
    (true,13,0);
    (false,13,0);
    (false,14,0);
    (true,14,0);
    (false,11,2);
    (true,11,2);
    (false,8,3);
    (true,8,3);
    (true,14,1);
    (false,14,1);
    (true,15,0);
    (true,7,3);
    (false,7,3);
    (false,15,0);
    (false,6,3);
    (false,9,3);
    (true,14,2);
    (true,9,3);
    (false,14,2);
    (true,18,2);
    (false,18,2);
    (true,11,3);
    (true,14,3);
    (true,18,3);
    (false,18,3);
    (false,14,3);
    (false,11,3);
    (false,10,3);
    (false,13,2);
    (true,13,2);
    (true,15,1);
    (false,15,1);
    (false,18,0);
    (true,17,1);
    (false,16,2);
    (true,16,2);
    (true,10,3);
    (false,17,1);
    (true,18,0);
    (true,12,3);
    (true,9,4);
    (false,16,0);
    (true,16,0);
    (true,16,3);
    (false,16,1);
    (false,16,3);
    (false,9,4);
    (false,12,3);
    (true,16,1);
    (true,13,3);
    (true,17,2);
    (true,12,4);
    (true,18,4);
    (true,17,0);
    (false,13,3);
    (false,17,2);
    (false,18,4);
    (false,12,4);
    (false,17,0)].

Definition state32_check tm :=
  if fast_drift_check tm 55 then true else
  if fast_static_state_check tm 55 38 then true else
  find_success (fun p => let '(mirror,period,width) := p in
    fast_tc_wait_check_state tm 55 38 mirror 93 period width) state32_profiles.

Theorem state32_check_sound : forall tm, state32_check tm = true ->
  forall q, FutureBeep tm q 55 -> BeepWindow tm q 55 38.
Proof.
  intros tm H; unfold state32_check in H.
  destruct (fast_drift_check tm 55) eqn:Ed.
  { exact (fast_drift_check_state_sound tm 55 Ed 38). }
  destruct (fast_static_state_check tm 55 38) eqn:E.
  - now apply fast_static_state_check_sound.
  - apply find_success_sound in H as ([[m p] w] & H).
    exact (fast_tc_wait_check_state_sound tm 55 38 m 93 p w H).
Qed.

Definition instr32_check tm :=
  if fast_drift_check tm 55 then true else
  if fast_static_instr_check tm 55 173 then true else
  if find_success (fun p => let '(mirror,period,width) := p in
    fast_tc_wait_check_tr tm 55 173 mirror 228 period width) instr32_profiles then true
  else hn_wait_check_tr tm 55 173 2 2 228 256 16.

Theorem instr32_check_sound : forall tm, instr32_check tm = true ->
  forall q, FutureBeepTr tm q 55 -> BeepWindowTr tm q 55 173.
Proof.
  intros tm H; unfold instr32_check in H.
  destruct (fast_drift_check tm 55) eqn:Ed.
  { exact (fast_drift_check_sound tm 55 Ed 173). }
  destruct (fast_static_instr_check tm 55 173) eqn:E.
  - now apply fast_static_instr_check_sound.
  - destruct (find_success _ instr32_profiles) eqn:Ec.
    + apply find_success_sound in Ec as ([[m p] w] & Hc).
      exact (fast_tc_wait_check_tr_sound tm 55 173 m 228 p w Hc).
    + exact (hn_wait_check_tr_sound tm 55 173 2 2 228 256 16 H).
Qed.
