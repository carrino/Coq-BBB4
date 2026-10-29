(** State-only acceptance must not be confused with instruction recurrence. *)
From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Pipeline
  OneStateReach OneStateBatch.
Import ListNotations.

Definition ore_survivor := machine_of_codes [5;11;4;0;14;8;11;11].
Example ore_survivor_checked : ore_auto_state ore_survivor=true.
Proof. vm_compute. reflexivity. Qed.
Theorem ore_survivor_state_zero : NonHalt ore_survivor /\ QHBound 0 ore_survivor.
Proof. apply ore_auto_state_sound, ore_survivor_checked. Qed.

Definition ore_blank_spinout := machine_of_codes [5;9;14;5;11;13;10;1].
Example ore_reject_blank_spinout : ore_auto_state ore_blank_spinout=false.
Proof. vm_compute. reflexivity. Qed.
Definition ore_opposing_trap := machine_of_codes [5;10;14;9;2;0;11;13].
Example ore_reject_opposing_trap : ore_auto_state ore_opposing_trap=false.
Proof. vm_compute. reflexivity. Qed.
Example ore_packing_roundtrip : ore_machine 3146646709%N =
  machine_of_codes [5;11;4;0;14;8;11;11].
Proof. vm_compute. reflexivity. Qed.

Definition ore_oscillator : TM := fun q _ => Some
  (match q with StA=>mkTrans S3 DR StB | StB=>mkTrans S3 DL StA end).
Definition ore_osc_a : cconf := (StA,([],S3,[S3])).
Definition ore_osc_b : cconf := (StB,([S3],S3,[])).
Lemma ore_oscillator_checked : ore_auto_state ore_oscillator=true.
Proof. vm_compute. reflexivity. Qed.
Lemma ore_osc_tail : forall n cc,
  cc=ore_osc_a \/ cc=ore_osc_b -> exists cc',
  csteps ore_oscillator n cc=Some cc' /\ (cc'=ore_osc_a \/ cc'=ore_osc_b).
Proof.
  induction n; intros cc H.
  - exists cc. auto.
  - destruct H as [-> | ->]; cbn [csteps].
    + change (exists cc', csteps ore_oscillator n ore_osc_b=Some cc' /\
        (cc'=ore_osc_a \/ cc'=ore_osc_b)). apply IHn; auto.
    + change (exists cc', csteps ore_oscillator n ore_osc_a=Some cc' /\
        (cc'=ore_osc_a \/ cc'=ore_osc_b)). apply IHn; auto.
Qed.
Lemma ore_osc_blank_instruction_quiet : QuietAfterTr ore_oscillator (StB,S0) 1.
Proof.
  split.
  - exists (lift (StB,([S3],S0,[]))). split.
    + rewrite <- lift_c0. apply csteps_lift. reflexivity.
    + reflexivity.
  - intros n Hn (c & Hr & Htg).
    destruct (ore_osc_tail (n-2) ore_osc_a (or_introl eq_refl)) as (cc&Htail&Hcc).
    assert (Hrun:csteps ore_oscillator n c0=Some cc).
    { replace n with (2+(n-2)) by lia. rewrite csteps_add.
      change (csteps ore_oscillator (n-2) ore_osc_a=Some cc). exact Htail. }
    pose proof (csteps_lift _ _ _ _ Hrun) as Hrun'. rewrite lift_c0,Hr in Hrun'.
    injection Hrun' as ->. destruct Hcc as [-> | ->]; discriminate.
Qed.
Theorem ore_state_zero_does_not_imply_instruction_zero :
  NonHalt ore_oscillator /\ QHBound 0 ore_oscillator /\ ~QHBoundTr 0 ore_oscillator.
Proof.
  destruct (ore_auto_state_sound _ ore_oscillator_checked) as [Hnh Hs].
  split; [exact Hnh|]. split; [exact Hs|].
  intro Hi. specialize (Hi _ _ ore_osc_blank_instruction_quiet). lia.
Qed.
