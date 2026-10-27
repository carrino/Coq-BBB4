(** State-only finite/history closure tiers. These constructors cannot select
    instruction acceptance or claim an instruction bound. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Pipeline StateOnlyCloseout
  FiniteCensus HistCensus.
Import ListNotations.

Inductive StateStage :=
  | StateFinite (n t fuel rounds : nat)
  | StateHistory (k n t fuel rounds : nat).
Definition stp_check (bound : N) tm cert := match cert with
  | StateFinite n t fuel rounds => fn_check_mode true bound bound tm n t fuel rounds
  | StateHistory k n t fuel rounds => hn_check_mode true bound bound tm k n t fuel rounds
  end.
Theorem stp_check_sound : forall bound tm cert,
  stp_check bound tm cert=true -> NonHalt tm /\ QHBound (N.to_nat bound) tm.
Proof.
  intros bound tm []; cbn [stp_check];
    [apply (fn_check_mode_sound true)|apply (hn_check_mode_sound true)].
Qed.
Fixpoint stp_unpack fuel (packed : N) : list nat := match fuel with
  | 0 => []
  | S f => N.to_nat (packed mod 17)%N :: stp_unpack f (packed/17)%N
  end.
Definition stp_machine packed := machine_of_codes (stp_unpack 8 packed).
Definition stp_batch_check bound cert (rows : list N) :=
  forallb (fun packed => stp_check bound (stp_machine packed) cert) rows.
Definition stp_board rows := map stp_machine rows.
Theorem stp_batch_state_sound : forall bound cert rows,
  stp_batch_check bound cert rows=true -> StateBoardSound (N.to_nat bound) (stp_board rows).
Proof.
  intros bound cert rows H family Hin tm Hle.
  apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  destruct (stp_check_sound _ _ _ H) as [Hnh Hb]. eapply state_bound_extend; eauto.
Qed.
Theorem stp_batch_nonhalt : forall bound cert rows,
  stp_batch_check bound cert rows=true -> forall family,
  In family (stp_board rows) -> NonHalt family.
Proof.
  intros bound cert rows H family Hin. apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  exact (proj1 (stp_check_sound _ _ _ H)).
Qed.
Print Assumptions stp_check_sound.
